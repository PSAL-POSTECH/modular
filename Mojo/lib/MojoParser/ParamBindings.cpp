//===----------------------------------------------------------------------===//
// Copyright (c) 2026, Modular Inc. All rights reserved.
//
// Licensed under the Apache License v2.0 with LLVM Exceptions:
// https://llvm.org/LICENSE.txt
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//===----------------------------------------------------------------------===//

#include "ParamBindings.h"
#include "ExprNodes.h"
#include "IREmitter.h"
#include "MojoUtils.h"
#include "ParamInf.h"
#include "ParserEvaluationContext.h"
#include "Traits.h"

#include "Mojo/KGENDialect/KGENAttrs.h"
#include "Mojo/KGENDialect/KGENUtils.h"
#include "Mojo/LITDialect/LITOps.h"
#include "Mojo/LITDialect/LITTypes.h"
#include "Mojo/LITDialect/LITUtils.h"
#include "Mojo/MojoParser/ASTDecl.h"
#include "Mojo/MojoParser/Constraints.h"
#include "Mojo/MojoParser/DeclResolver.h"
#include "Mojo/MojoParser/IRValues.h"
#include "Mojo/MojoParser/SharedState.h"
#include "Support/Compiler/OperationUtils.h"
#include "Support/STLExtras.h"

using namespace M;
using namespace M::KGEN;
using namespace M::KGEN::LIT;

void LIT::emitUnprovableConstraintsFromFitness(
    ArrayRef<ConstraintAttr> unprovableConstraints, SharedState &shared,
    SMLoc exprLoc, ASTDecl *declIfKnown) {
  if (unprovableConstraints.empty())
    return;

  std::string baseName;
  if (declIfKnown)
    baseName = "'" + declIfKnown->getUserNameIfOperation()->str() + "'";
  else
    baseName = "parametric value";

  MojoInflightDiag diag = shared.emitError(exprLoc)
                          << "invalid bindings for " << baseName
                          << ": lacking evidence to prove correctness";
  if (declIfKnown)
    diag.attachNote(declIfKnown->getLoc())
        << "cannot prove constraint" << plural(unprovableConstraints.size());
  for (auto constraint : unprovableConstraints)
    LIT::emitConstraintInconclusive(shared.getDeclResolver(), diag, constraint);
}

//===----------------------------------------------------------------------===//
// ParamBindings
//===----------------------------------------------------------------------===//

ParamBindings::ParamBindings(ASTDecl &declScope, const ExprNode *expr)
    : declScope(declScope), shared(declScope.getShared()),
      parameters(CallSyntax::kParamBindings, expr, EC_InvalidContext) {}

/// Replace our bindings with another set.  This can't be done with operator=
/// because we have
void ParamBindings::operator=(ParamBindings &&other) {
  parameters = std::move(other.parameters);
  additionalConstraints = std::move(other.additionalConstraints);
  bindingKind = other.bindingKind;
}

SMLoc ParamBindings::getExprLoc() const { return getExpr()->getLoc(); }

void ParamBindings::add(const ExprNode *expr, AnyValue value, StringAttr name) {
  assert(!isa_and_nonnull<EllipsisAttr>(value.getIfPValue().get()) &&
         "ellipsis is not allowed as a binding value, set the BindingKind to "
         "kWithEllipsis instead");
  parameters.add(name, {value, expr},
                 name ? ArgUnpackStyle::kKeyword : ArgUnpackStyle::kPositional);
}

void ParamBindings::append(const ParamBindings &other) {
  llvm::append_range(parameters.values, other.parameters.values);
  llvm::append_range(additionalConstraints, other.additionalConstraints);
  bindingKind = other.bindingKind;
}

static bool isReferenceFromOwnFnBody(ASTDecl &fnDecl, ASTDecl &useScope) {
  auto *defDecl = dyn_cast<DefASTDecl>(&fnDecl);
  FnOp funcOp = defDecl ? defDecl->getOp() : nullptr;
  if (!funcOp || !isa_and_nonnull<FnOp>(funcOp->getParentOp()))
    return false;

  for (ASTDecl *scope = &useScope; scope; scope = scope->getParentDecl()) {
    if (scope == &fnDecl)
      return true;
  }
  return false;
}

/// The concrete function a bound parameter value names, or null when it is
/// still symbolic (a forwarded parameter, a trait witness, ...).
static SymbolRefAttr getBoundFuncSymbol(TypedAttr value) {
  while (value) {
    value = ParamOperatorAttr::stripRebind(value);
    if (auto bind = dyn_cast<BindParamsAttr>(value)) {
      value = bind.getGenerator();
      continue;
    }
    if (auto callable = dyn_cast<CallableSymbolAttrInterface>(value))
      return callable.getSymbol();
    if (auto sym = dyn_cast<FuncSymbolAttr>(value))
      return sym.getSymbol();
    if (auto lit = sugarDynCast<FnLiteralTypeGeneratorType>(value.getType()))
      return lit.getSymbolConstantAttr().getSymbol();
    return {};
  }
  return {};
}

/// Fractra: a parameter declared `f: @role def ...` only binds a function
/// decorated `@role`.
static LogicalResult checkParamRoles(FnOp funcOp, ASTDecl &fnDecl,
                                     SharedState &shared,
                                     const VerifiedParamBindings &verified,
                                     SMLoc useLoc) {
  auto roles = funcOp->getAttrOfType<DictionaryAttr>("fractra.param_roles");
  if (!roles || !verified)
    return success();
  ArrayRef<TypedAttr> values = verified.getValues();
  auto pogs = fnDecl.getDeclFullSignature().getParamListAttrs().getPogs();
  for (auto [pog, value] : llvm::zip(pogs, values)) {
    auto want = roles.getAs<StringAttr>(pog.getName());
    if (!want)
      continue;
    SymbolRefAttr symbol = getBoundFuncSymbol(value);
    if (!symbol)
      continue;
    auto *bound = dyn_cast_or_null<DefASTDecl>(
        shared.resolveAndGetFuncDecl(symbol, useLoc));
    if (!bound)
      continue;
    auto have = bound->getOp()->getAttrOfType<StringAttr>("fractra.role");
    if (have == want)
      continue;
    auto diag = shared.emitError(useLoc, "parameter '")
                << pog.getName().getValue() << "' of '"
                << funcOp.getDeclName().getValue() << "' requires a '@"
                << want.getValue() << "' function, but '"
                << bound->getOp().getDeclName().getValue() << "' is "
                << (have ? "'@" + have.getValue().str() + "'"
                         : std::string("not a Fractra role"));
    diag.attachNote(*bound) << "declared here";
    return failure();
  }
  return success();
}

/// Utility function to perform substitutions of the bindings into the symbol
/// for the given function declaration. It returns the resultant
/// SymbolConstantAttr or produces an error message and returns null.
TypedAttr LIT::getBoundConstAttrForFn(ASTDecl &fnDecl, SharedState &shared,
                                      const VerifiedParamBindings &verified,
                                      ASTDecl &useScope, SMLoc useLoc) {
  if (auto *defDecl = dyn_cast<DefASTDecl>(&fnDecl); defDecl) {
    FnOp funcOp = defDecl->getOp();
    if (failed(checkParamRoles(funcOp, fnDecl, shared, verified, useLoc)))
      return {};
    if (isReferenceFromOwnFnBody(fnDecl, useScope)) {
      StringRef name = funcOp.getDeclName().getValue();
      auto diag = shared.emitError(
                      useLoc, "recursive references to nested functions are "
                              "not supported; define '")
                  << name << "' at file scope";
      diag.attachNote(fnDecl) << "nested function declared here";
      return {};
    }

    assert(!isa<TraitDeclOp>(funcOp->getParentOp()) &&
           "trait witness should always retrieved from a witness entry");
    return funcOp.getFuncLiteralGenerator(
        shared.getEvaluationContext(), verified.asAttr(),
        verified.getDischargedBodyConstraints());
  }

  auto *witnessEntry = dyn_cast<WitnessASTDecl>(&fnDecl);
  assert(witnessEntry);

  ArrayRef<TypedAttr> verifiedValues = verified.getValues();
  // Must at least have one `_Self` parameter.
  assert(!verifiedValues.empty());

  TypedAttr selfExpr = verifiedValues[0];
  auto signature =
      cast<FnTypeGeneratorType>(witnessEntry->getWitnessEntry().witnessType);

  SmallVector<TypedAttr> paramValues;
  paramValues.push_back(selfExpr);
  for (Type t : signature.getInputParamTypes().drop_front())
    paramValues.push_back(UnboundAttr::get(t));

  TraitSymbolAttr witnessFor = witnessEntry->traitSymbol;

  // Get the signature with only `_Self` bound.
  signature = signature.getSpecializedGenerator(paramValues,
                                                &shared.getEvaluationContext());

  TypedAttr fnRef = shared.getEvaluationContext().getAndFold<GetWitnessAttr>(
      selfExpr, witnessFor, witnessEntry->getWitnessEntry().witnessName,
      signature);

  ArrayRef<TypedAttr> remainingParamValues = verifiedValues.drop_front();
  const llvm::BitVector &discharged = verified.getDischargedBodyConstraints();
  DenseBoolArrayAttr dischargedAttr =
      KGEN::getDenseBoolArrayAttr(fnRef.getContext(), discharged);
  return BindParamsAttr::get(fnRef.getContext(), fnRef, remainingParamValues,
                             dischargedAttr, &shared.getEvaluationContext());
}

TypedAttr LIT::getBoundConstAttrForFn(ASTDecl &fnDecl,
                                      const ParamBindings &unverified) {
  VerifiedParamBindings verifiedBindings;
  if (!unverified.empty()) {
    FnTypeGeneratorType signature = fnDecl.getDeclFullSignature();
    // Check that the signature can be rebound with our set of bindings.
    ParamInf inference(unverified, signature.getInputParamTypes(),
                       signature.getParamListAttrs(),
                       /*allowImplicitConversions=*/true, &fnDecl,
                       /*discardError=*/false);
    verifiedBindings = inference.inferForStruct();
    if (!verifiedBindings)
      return {};
  }
  return getBoundConstAttrForFn(fnDecl, unverified.shared, verifiedBindings,
                                unverified.declScope, unverified.getExprLoc());
}

void ParamBindings::dump() const { llvm::errs() << parameters << "\n"; }
