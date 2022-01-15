grammar edu:umn:cs:melt:exts:ableC:halide:abstractsyntax;

imports silver:langutil;
imports silver:langutil:pp;

imports edu:umn:cs:melt:ableC:abstractsyntax:host;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction;
imports edu:umn:cs:melt:ableC:abstractsyntax:overloadable;
imports edu:umn:cs:melt:ableC:abstractsyntax:env;

global builtin::Location = builtinLoc("halide");

abstract production transformStmt
top::Stmt ::= s::Stmt t::Transformation
{
  top.pp =
    ppConcat([pp"transform ", braces(nestlines(2, s.pp)), pp" by ", braces(nestlines(2, t.pp))]);
  top.functionDefs := [];
  top.labelDefs := [];
  
  local normalizedS::Stmt = s.normalizeLoops;
  normalizedS.env = s.env;
  normalizedS.controlStmtContext = s.controlStmtContext;
  
  t.iterStmtIn = stmtToIterStmt(normalizedS);
  
  local transResult::IterStmt = t.iterStmtOut;
  transResult.env = top.env;
  transResult.controlStmtContext = top.controlStmtContext;
  
  forwards to
    if !null(s.errors)
    then warnStmt(s.errors)
    else if !null(t.errors)
    then warnStmt(t.errors)
    else if !null(normalizedS.errors)
    then warnStmt(normalizedS.errors) -- Shouldn't happen
    else if !null(transResult.errors)
    then warnStmt(transResult.errors) -- Shouldn't happen
    else transResult.hostTrans;
}

partial strategy attribute simplifyNumericExprStep =
{-  rule on Expr of
  | e -> unsafeTrace(e, print(show(80, e.pp) ++ "\n\n", unsafeIO()))
  end <*-}
  rule on Expr of
  -- Simplify expressions as much as possible
  | ableC_Expr { ($Expr{e}) } -> e
  | ableC_Expr { host::-$Expr{e} } when e.integerConstantValue.isJust ->
    mkIntConst(-e.integerConstantValue.fromJust, builtin)
  | ableC_Expr { $Expr{e1} host::+ $Expr{e2} }
    when e1.integerConstantValue.isJust && e2.integerConstantValue.isJust ->
    mkIntConst(e1.integerConstantValue.fromJust + e2.integerConstantValue.fromJust, builtin)
  | ableC_Expr { $Expr{e1} host::- $Expr{e2} }
    when e1.integerConstantValue.isJust && e2.integerConstantValue.isJust ->
    mkIntConst(e1.integerConstantValue.fromJust - e2.integerConstantValue.fromJust, builtin)
  | ableC_Expr { $Expr{e1} host::* $Expr{e2} }
    when e1.integerConstantValue.isJust && e2.integerConstantValue.isJust ->
    mkIntConst(e1.integerConstantValue.fromJust * e2.integerConstantValue.fromJust, builtin)
  | ableC_Expr { $Expr{e1} host::/ $Expr{e2} }
    when e1.integerConstantValue.isJust && e2.integerConstantValue.isJust && e1.integerConstantValue.fromJust != 0 ->
    mkIntConst(e1.integerConstantValue.fromJust / e2.integerConstantValue.fromJust, builtin)
  end;

strategy attribute simplifyNumericExpr = innermost(simplifyNumericExprStep);
partial strategy attribute simplifyLoopExprs =
  forDeclStmt(simplifyNumericExpr, simplifyNumericExpr, simplifyNumericExpr, id);

attribute simplifyNumericExprStep, simplifyNumericExpr, simplifyLoopExprs occurs on
  Stmt, Decl, Declarators, Declarator, MaybeInitializer, Initializer, MaybeExpr, Expr;
propagate simplifyNumericExprStep, simplifyNumericExpr, simplifyLoopExprs on
  Stmt, Decl, Declarators, Declarator, MaybeInitializer, Initializer, MaybeExpr, Expr;

partial strategy attribute preprocessLoop =
  rule on Stmt of
  -- Normalize condition orderings
  | ableC_Stmt { for ($BaseTypeExpr{t} $Name{i1} = host::($Expr{initial}); $Expr{limit} host::< host::$Name{i2}; $Expr{iter}) $Stmt{b} }
      when i1.name == i2.name ->
    ableC_Stmt { for ($BaseTypeExpr{t} $Name{i1} = host::($Expr{initial}); host::$Name{i2} host::> $Expr{limit}; $Expr{iter}) $Stmt{b} }
  | ableC_Stmt { for ($BaseTypeExpr{t} $Name{i1} = host::($Expr{initial}); $Expr{limit} host::> host::$Name{i2}; $Expr{iter}) $Stmt{b} }
      when i1.name == i2.name ->
    ableC_Stmt { for ($BaseTypeExpr{t} $Name{i1} = host::($Expr{initial}); host::$Name{i2} host::< $Expr{limit}; $Expr{iter}) $Stmt{b} }
  | ableC_Stmt { for ($BaseTypeExpr{t} $Name{i1} = host::($Expr{initial}); $Expr{limit} host::<= host::$Name{i2}; $Expr{iter}) $Stmt{b} }
      when i1.name == i2.name ->
    ableC_Stmt { for ($BaseTypeExpr{t} $Name{i1} = host::($Expr{initial}); host::$Name{i2} host::>= $Expr{limit}; $Expr{iter}) $Stmt{b} }
  | ableC_Stmt { for ($BaseTypeExpr{t} $Name{i1} = host::($Expr{initial}); $Expr{limit} host::>= host::$Name{i2}; $Expr{iter}) $Stmt{b} }
      when i1.name == i2.name ->
    ableC_Stmt { for ($BaseTypeExpr{t} $Name{i1} = host::($Expr{initial}); host::$Name{i2} host::<= $Expr{limit}; $Expr{iter}) $Stmt{b} }
  
  -- Normalize condition operators
  | ableC_Stmt { for ($Decl{init} host::$Name{i} host::<= $Expr{limit}; $Expr{iter}) $Stmt{b} } ->
    ableC_Stmt { for ($Decl{init} host::$Name{i} host::< $Expr{limit} + 1; $Expr{iter}) $Stmt{b} }
  | ableC_Stmt { for ($Decl{init} host::$Name{i} host::> $Expr{limit}; $Expr{iter}) $Stmt{b} } ->
    ableC_Stmt { for ($Decl{init} host::$Name{i} host::>= $Expr{limit} + 1; $Expr{iter}) $Stmt{b} }
  
  -- Expand increment/decrement operators
  | ableC_Stmt { for ($Decl{init} $Expr{cond}; host::$Name{i} host::++) $Stmt{b} } ->
    ableC_Stmt { for ($Decl{init} $Expr{cond}; host::$Name{i} host::+= 1) $Stmt{b} }
  | ableC_Stmt { for ($Decl{init} $Expr{cond}; host::$Name{i} host::--) $Stmt{b} } ->
    ableC_Stmt { for ($Decl{init} $Expr{cond}; host::$Name{i} host::-= 1) $Stmt{b} }
  end;

-- Transformation to perform a renaming over anything
-- Not capture-avoiding, but that's OK!
-- If we rename a shadowed name, then we will also rename the shadowing declaration.
autocopy attribute targetName::String;
autocopy attribute replacement::String;
strategy attribute renamed =
  allTopDown(
    rule on top::Name of
    | name(n) when n == top.targetName -> name(top.replacement, location=top.location)
    end);

attribute targetName, replacement, renamed occurs on
  Name, MaybeName,
  GlobalDecls, Decls, Decl, Declarators, Declarator, FunctionDecl, Parameters, ParameterDecl, StructDecl, UnionDecl, EnumDecl, StructItemList, EnumItemList, StructItem, StructDeclarators, StructDeclarator, EnumItem,
  MemberDesignator,
  Expr, GenericAssocs, GenericAssoc,
  TypeName, BaseTypeExpr, TypeModifierExpr, TypeNames,
  NumericConstant,
  MaybeExpr, Exprs, ExprOrTypeName,
  Stmt,
  MaybeInitializer, Initializer, InitList, Init, Designator,
  SpecialSpecifiers;
propagate renamed on
  Name, MaybeName,
  GlobalDecls, Decls, Decl, Declarators, Declarator, FunctionDecl, Parameters, ParameterDecl, StructDecl, UnionDecl, EnumDecl, StructItemList, EnumItemList, StructItem, StructDeclarators, StructDeclarator, EnumItem,
  MemberDesignator,
  Expr, GenericAssocs, GenericAssoc,
  TypeName, BaseTypeExpr, TypeModifierExpr, TypeNames,
  NumericConstant,
  MaybeExpr, Exprs, ExprOrTypeName,
  Stmt,
  MaybeInitializer, Initializer, InitList, Init, Designator,
  SpecialSpecifiers;

partial strategy attribute transLoop =
  rule on Stmt of
  -- Restore increment operator on loops that are otherwise-normal
  | ableC_Stmt {
      for ($BaseTypeExpr{t} $Name{i1} = host::(0); host::$Name{i2} host::< $Expr{n}; host::$Name{i3} host::+= 1) $Stmt{b}
    } when i1.name == i2.name && i1.name == i3.name ->
    ableC_Stmt {
      for ($BaseTypeExpr{t} $Name{i1} = host::(0); host::$Name{i2} host::< $Expr{n}; host::$Name{i3} host::++) $Stmt{b}
    }
  
  -- Normalize loops with nonstandard initial or step values
  | ableC_Stmt {
      for ($BaseTypeExpr{t} $Name{i1} = host::($Expr{initial}); host::$Name{i2} host::< $Expr{limit}; host::$Name{i3} host::+= $Expr{step})
        $Stmt{b}
    } when i1.name == i2.name && i1.name == i3.name && initial.isSimple && step.isSimple ->
      let newName::String = s"_iter_${i1.name}_${toString(genIntT())}"
      in ableC_Stmt {
        for ($BaseTypeExpr{t} $Name{i1} = host::(0); host::$Name{i2} host::< ($Expr{limit} - $Expr{initial}) / $Expr{step}; host::$Name{i3} host::++) {
          typeof($Name{i1}) $name{newName} = host::($Expr{initial} + $Name{i1} * $Expr{step});
          $Stmt{decorate b with { targetName = i1.name; replacement = newName; env = top.env; controlStmtContext = top.controlStmtContext; }.renamed}
        }
      }
      end
  
  -- Normalize "backwards" loops, possibly with with nonstandard initial or step values
  | ableC_Stmt {
      for ($BaseTypeExpr{t} $Name{i1} = host::($Expr{initial}); host::$Name{i2} host::>= $Expr{limit}; host::$Name{i3} host::-= $Expr{step})
        $Stmt{b}
    } when i1.name == i2.name && i1.name == i3.name && initial.isSimple && step.isSimple ->
      let newName::String = s"_iter_${i1.name}_${toString(genIntT())}"
      in ableC_Stmt {
        for ($BaseTypeExpr{t} $Name{i1} = host::(0); host::$Name{i2} host::< ($Expr{initial} - $Expr{limit} + 1) / $Expr{step}; host::$Name{i3} host::++) {
          typeof($Name{i1}) $name{newName} = host::($Expr{initial} - $Name{i1} * $Expr{step});
          $Stmt{decorate b with { targetName = i1.name; replacement = newName; env = top.env; controlStmtContext = top.controlStmtContext; }.renamed}
        }
      }
      end
  end;

strategy attribute normalizeLoops =
  downUp(
    try(simplifyLoopExprs <* repeat(preprocessLoop)),
    try(transLoop <* simplifyLoopExprs));

attribute preprocessLoop, transLoop, normalizeLoops occurs on Stmt;
propagate preprocessLoop, transLoop, normalizeLoops on Stmt;

function stmtToIterStmt
IterStmt ::= s::Decorated Stmt
{
  return
    case s of
    | nullStmt() -> nullIterStmt()
    | seqStmt(s1, s2) -> seqIterStmt(stmtToIterStmt(s1), stmtToIterStmt(s2))
    | compoundStmt(s1) -> stmtToIterStmt(s1)
    | ableC_Stmt { if ($Expr{c}) $Stmt{t} else $Stmt{e} } ->
      condIterStmt(c, stmtToIterStmt(t), stmtToIterStmt(e))
    | ableC_Stmt {
        for ($BaseTypeExpr{t} $Name{i1} = host::(0); host::$Name{i2} host::< $Expr{n}; host::$Name{i3} host::++)
          $Stmt{b}
      } when i1.name == i2.name && i1.name == i3.name ->
      forIterStmt(t, baseTypeExpr(), i1, n, stmtToIterStmt(b))
    | s -> stmtIterStmt(new(s))
    end;
}

abstract production multiForStmt
top::Stmt ::= ivs::IterVars body::Stmt
{
  top.pp = pp"forall (${ivs.pp}) ${braces(nestlines(2, body.pp))}";
  top.functionDefs := [];
  top.labelDefs := [];
  
  ivs.forIterStmtBody = stmtIterStmt(body);
  forwards to ivs.forIterStmtTrans.hostTrans;
}

monoid attribute iterDefs::[Def] with [], ++;
synthesized attribute hostTrans::Stmt;

nonterminal IterStmt with pp, errors, defs, iterDefs, hostTrans, env, controlStmtContext;

propagate iterDefs on IterStmt;

abstract production nullIterStmt
top::IterStmt ::= 
{
  propagate errors, defs;
  top.pp = notext();
  top.hostTrans = nullStmt();
}

abstract production seqIterStmt
top::IterStmt ::= h::IterStmt t::IterStmt
{
  propagate errors, defs;
  top.pp = ppConcat([ h.pp, line(), t.pp ]);
  top.hostTrans = seqStmt(h.hostTrans, t.hostTrans);
  
  t.env = addEnv(h.defs, h.env);
}

abstract production compoundIterStmt
top::IterStmt ::= is::IterStmt
{
  propagate errors;
  top.pp = braces(nestlines(2, is.pp));
  top.defs := [];
  top.hostTrans = compoundStmt(is.hostTrans);
  
  is.env = openScopeEnv(top.env);
}

abstract production stmtIterStmt
top::IterStmt ::= s::Stmt
{
  propagate errors, defs;
  top.pp = braces(braces(nestlines(2, s.pp)));
  top.hostTrans = s;
}

abstract production condIterStmt
top::IterStmt ::= cond::Expr th::IterStmt el::IterStmt
{
  propagate errors, defs;
  top.pp = pp"if (${cond.pp})${nestlines(2, th.pp)} else ${nestlines(2, el.pp)}";
  top.hostTrans = ifStmt(cond, th.hostTrans, el.hostTrans);
}

abstract production forIterStmt
top::IterStmt ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr body::IterStmt
{
  top.pp = pp"for (${ppConcat([bty.pp, space(), mty.lpp, n.pp, mty.rpp])} : ${cutoff.pp}) ${braces(nestlines(2, body.pp))}";
  top.errors := bty.errors ++ d.errors ++ cutoff.errors ++ body.errors;
  top.errors <- n.valueRedeclarationCheckNoCompatible;
  
  production d::Declarator =
    declarator(
      n, mty, nilAttribute(),
      justInitializer(exprInitializer(ableC_Expr {0}, location=builtin)));
  d.env = openScopeEnv(top.env);
  d.baseType = bty.typerep;
  d.typeModifierIn = bty.typeModifier;
  d.isTopLevel = false;
  d.isTypedef = false;
  d.givenStorageClasses = nilStorageClass();
  d.givenAttributes = nilAttribute();
  d.controlStmtContext = top.controlStmtContext;
  
  top.defs := [];
  top.iterDefs <- [valueDef(n.name, declaratorValueItem(d))];
  top.hostTrans =
    ableC_Stmt {
      for ($Decl{
        variableDecls(
          nilStorageClass(), nilAttribute(),
          bty,
          consDeclarator(d, nilDeclarator()))} $Name{n} < $Expr{cutoff}; $Name{n}++)
        $Stmt{body.hostTrans}
    };
  
  bty.givenRefId = nothing();
  body.env = addEnv(d.defs, openScopeEnv(top.env));
}

abstract production parallelForIterStmt
top::IterStmt ::= numThreads::Maybe<Integer> bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr body::IterStmt
{
  local numThreadsPP::Document =
    case numThreads of
    | just(n) -> parens(text(toString(n)))
    | nothing() -> notext()
    end;
  top.pp = pp"for parallel${numThreadsPP} (${ppConcat([bty.pp, space(), mty.lpp, n.pp, mty.rpp])} : ${cutoff.pp}) ${braces(nestlines(2, body.pp))}";
  top.errors := bty.errors ++ d.errors ++ cutoff.errors ++ body.errors;
  top.errors <- n.valueRedeclarationCheckNoCompatible;
  
  production d::Declarator = declarator(n, mty, nilAttribute(), nothingInitializer());
  d.env = openScopeEnv(top.env);
  d.baseType = bty.typerep;
  d.typeModifierIn = bty.typeModifier;
  d.isTopLevel = false;
  d.isTypedef = false;
  d.givenStorageClasses = nilStorageClass();
  d.givenAttributes = nilAttribute();
  d.controlStmtContext = top.controlStmtContext;
  
  top.defs := [];
  
  {- TODO: We don't right now have a way to insert pragmas via abstract syntax, and OpenMP is
   - rather picky about the loop variable being declared in the loop and extra parentheses in the
   - predicate, so we need to resort to some hacks with txtStmt for now.
   -}
  top.hostTrans =
    compoundStmt(
      foldStmt([
        declStmt( -- Still re-declare the loop variable in the ast, so it shows up in env for the host error check
          variableDecls(
            nilStorageClass(), nilAttribute(),
            bty,
            consDeclarator(d, nilDeclarator()))),
        case numThreads of
          just(n) -> txtStmt(s"#pragma omp parallel for num_threads(${toString(n)})")
        | nothing() -> txtStmt("#pragma omp parallel for")
        end,
        txtStmt(s"for (${show(80, bty.pp)} ${show(80, head(d.pps))} = 0; ${n.name} < ${show(80, cutoff.pp)}; ${n.name}++)"),
        compoundStmt(body.hostTrans)]));
  
  bty.givenRefId = nothing();
  
  body.env = addEnv(d.defs, openScopeEnv(top.env));
}

abstract production vectorForIterStmt
top::IterStmt ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr body::IterStmt
{
  top.pp = pp"for vector (${ppConcat([bty.pp, space(), mty.lpp, n.pp, mty.rpp])} : ${cutoff.pp}) ${braces(nestlines(2, body.pp))}";
  top.errors := bty.errors ++ d.errors ++ cutoff.errors ++ body.errors;
  top.errors <- n.valueRedeclarationCheckNoCompatible;
  
  production d::Declarator = declarator(n, mty, nilAttribute(), nothingInitializer());
  d.env = openScopeEnv(top.env);
  d.baseType = bty.typerep;
  d.typeModifierIn = bty.typeModifier;
  d.isTopLevel = false;
  d.isTypedef = false;
  d.givenStorageClasses = nilStorageClass();
  d.givenAttributes = nilAttribute();
  d.controlStmtContext = top.controlStmtContext;
  
  top.defs := [];
  
  {- TODO: We don't right now have a way to insert pragmas via abstract syntax, and OpenMP is
   - rather picky about the loop variable being declared in the loop and extra parentheses in the
   - predicate, so we need to resort to some hacks with txtStmt for now.
   -}
  top.hostTrans =
    compoundStmt(
      foldStmt([
        declStmt( -- Still re-declare the loop variable in the ast, so it shows up in env for the host error check
          variableDecls(
            nilStorageClass(), nilAttribute(),
            bty,
            consDeclarator(d, nilDeclarator()))),
        txtStmt("#pragma omp simd"),
        txtStmt(s"for (${show(80, bty.pp)} ${show(80, head(d.pps))} = 0; ${n.name} < ${show(80, cutoff.pp)}; ${n.name}++)"),
        compoundStmt(body.hostTrans)]));
  
  bty.givenRefId = nothing();
  
  body.env = addEnv(d.defs, openScopeEnv(top.env));
}

synthesized attribute iterVarNames::[Name];

synthesized attribute forIterStmtTrans::IterStmt;
inherited attribute forIterStmtBody::IterStmt;

nonterminal IterVars with pp, errors, iterVarNames, forIterStmtTrans, forIterStmtBody, env,
  controlStmtContext;

propagate errors on IterVars;

abstract production consIterVar
top::IterVars ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr rest::IterVars
{
  top.pp = ppConcat([bty.pp, space(), mty.lpp, n.pp, mty.rpp, text(" : "), cutoff.pp, comma(), space(), rest.pp]);
  top.errors <-
    case cutoff.integerConstantValue of
    | just(n) when n < 1 -> [err(cutoff.location, "Split loop size must be >= 1")]
    | _ -> []
    end;
  top.iterVarNames = n :: rest.iterVarNames;
  
  top.forIterStmtTrans = forIterStmt(bty, mty, n, cutoff, rest.forIterStmtTrans);
  rest.forIterStmtBody = top.forIterStmtBody;
  
  bty.givenRefId = nothing();
  
  mty.baseType = bty.typerep;
  mty.typeModifierIn = bty.typeModifier;
}

abstract production consAnonIterVar
top::IterVars ::= cutoff::Expr rest::IterVars
{
  top.pp = ppConcat([cutoff.pp, comma(), rest.pp]);
  forwards to
    consIterVar(
      directTypeExpr(cutoff.typerep),
      baseTypeExpr(),
      name("_iter_var_" ++ toString(genIntT()), location=builtin),
      cutoff, rest);
}

abstract production nilIterVar
top::IterVars ::= 
{
  top.pp = notext();
  top.iterVarNames = [];
  top.forIterStmtTrans = top.forIterStmtBody;
}

synthesized attribute iterVarName::Name;

inherited attribute forIterStmtCutoff::Expr;

nonterminal IterVar with pp, errors, iterVarName, forIterStmtTrans, forIterStmtCutoff,
  forIterStmtBody, env, controlStmtContext;

propagate errors on IterVar;

abstract production iterVar
top::IterVar ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name
{
  top.pp = ppConcat([bty.pp, space(), mty.lpp, n.pp, mty.rpp]);
  top.iterVarName = n;
  top.forIterStmtTrans = forIterStmt(bty, mty, n, top.forIterStmtCutoff, top.forIterStmtBody);
  
  bty.givenRefId = nothing();
  
  mty.baseType = bty.typerep;
  mty.typeModifierIn = bty.typeModifier;
}
