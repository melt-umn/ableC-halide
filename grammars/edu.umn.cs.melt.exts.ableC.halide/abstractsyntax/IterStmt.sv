grammar edu:umn:cs:melt:exts:ableC:halide:abstractsyntax;

imports silver:langutil;
imports silver:langutil:pp;
imports silver:rewrite as s;

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
  
  local normalizedS::Stmt = rewriteWith(normalizeLoops, new(s)).fromJust;
  normalizedS.env = s.env;
  normalizedS.returnType = s.returnType;
  
  t.iterStmtIn = stmtToIterStmt(normalizedS);
  
  local transResult::IterStmt = t.iterStmtOut;
  transResult.env = top.env;
  transResult.returnType = top.returnType;
  
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

function rename
s:Strategy ::= n1::String n2::String
{
  return s:topDown(s:try(
    rule on Name of
    | name(n, location=l) when n == n1 -> name(n2, location=l)
    end));
}

function isSimple
Boolean ::= e::Expr
{
  -- Avoid decorating with the full env during rewriting.
  -- This will never make an otherwise-not-simple AST appear simple.
  e.env = emptyEnv();
  e.returnType = nothing();
  return e.isSimple;
}

function isIntConst
Boolean ::= e::Expr
{
  -- Avoid decorating with the full env during rewriting.
  -- This will never make an non-int-constant AST appear to be an int constant.
  e.env = emptyEnv();
  e.returnType = nothing();
  return e.integerConstantValue.isJust;
}

function intValue
Integer ::= e::Expr
{
  -- Avoid decorating with the full env during rewriting.
  -- This will never make an non-int-constant AST appear to be an int constant.
  e.env = emptyEnv();
  e.returnType = nothing();
  return e.integerConstantValue.fromJust;
}

global simplifyNumericExprStep::s:Strategy =
  rule on Expr of
  -- Simplify expressions as much as possible
  | ableC_Expr { ($Expr{e}) } -> e
  | ableC_Expr { -$Expr{e} } when isIntConst(e) -> mkIntConst(-intValue(e), builtin)
  | ableC_Expr { $Expr{e1} + $Expr{e2} } when isIntConst(e1) && isIntConst(e2) ->
    mkIntConst(intValue(e1) + intValue(e2), builtin)
  | ableC_Expr { $Expr{e1} - $Expr{e2} } when isIntConst(e1) && isIntConst(e2) ->
    mkIntConst(intValue(e1) - intValue(e2), builtin)
  | ableC_Expr { $Expr{e1} * $Expr{e2} } when isIntConst(e1) && isIntConst(e2) ->
    mkIntConst(intValue(e1) * intValue(e2), builtin)
  | ableC_Expr { $Expr{e1} / $Expr{e2} } when isIntConst(e1) && isIntConst(e2) && intValue(e2) > 0 ->
    mkIntConst(intValue(e1) / intValue(e2), builtin)
  end;

global simplifyNumericExpr::s:Strategy = s:innermost(simplifyNumericExprStep);
global simplifyLoopExprs::s:Strategy =
  traverse forDeclStmt(simplifyNumericExpr, simplifyNumericExpr, simplifyNumericExpr, _);

global preprocessLoop::s:Strategy =
  rule on Stmt of
  -- Normalize condition orderings
  | ableC_Stmt { for ($BaseTypeExpr{t} $Name{i1} = $Expr{initial}; $Expr{limit} < $Name{i2}; $Expr{iter}) $Stmt{b} }
      when i1.name == i2.name ->
    ableC_Stmt { for ($BaseTypeExpr{t} $Name{i1} = $Expr{initial}; $Name{i2} > $Expr{limit}; $Expr{iter}) $Stmt{b} }
  | ableC_Stmt { for ($BaseTypeExpr{t} $Name{i1} = $Expr{initial}; $Expr{limit} > $Name{i2}; $Expr{iter}) $Stmt{b} }
      when i1.name == i2.name ->
    ableC_Stmt { for ($BaseTypeExpr{t} $Name{i1} = $Expr{initial}; $Name{i2} < $Expr{limit}; $Expr{iter}) $Stmt{b} }
  | ableC_Stmt { for ($BaseTypeExpr{t} $Name{i1} = $Expr{initial}; $Expr{limit} <= $Name{i2}; $Expr{iter}) $Stmt{b} }
      when i1.name == i2.name ->
    ableC_Stmt { for ($BaseTypeExpr{t} $Name{i1} = $Expr{initial}; $Name{i2} >= $Expr{limit}; $Expr{iter}) $Stmt{b} }
  | ableC_Stmt { for ($BaseTypeExpr{t} $Name{i1} = $Expr{initial}; $Expr{limit} >= $Name{i2}; $Expr{iter}) $Stmt{b} }
      when i1.name == i2.name ->
    ableC_Stmt { for ($BaseTypeExpr{t} $Name{i1} = $Expr{initial}; $Name{i2} <= $Expr{limit}; $Expr{iter}) $Stmt{b} }
  
  -- Normalize condition operators
  | ableC_Stmt { for ($Decl{init} $Name{i} <= $Expr{limit}; $Expr{iter}) $Stmt{b} } ->
    ableC_Stmt { for ($Decl{init} $Name{i} < $Expr{limit} + 1; $Expr{iter}) $Stmt{b} }
  | ableC_Stmt { for ($Decl{init} $Name{i} > $Expr{limit}; $Expr{iter}) $Stmt{b} } ->
    ableC_Stmt { for ($Decl{init} $Name{i} >= $Expr{limit} + 1; $Expr{iter}) $Stmt{b} }
  
  -- Expand increment/decrement operators
  | ableC_Stmt { for ($Decl{init} $Expr{cond}; $Name{i}++) $Stmt{b} } ->
    ableC_Stmt { for ($Decl{init} $Expr{cond}; $Name{i} += 1) $Stmt{b} }
  | ableC_Stmt { for ($Decl{init} $Expr{cond}; $Name{i}--) $Stmt{b} } ->
    ableC_Stmt { for ($Decl{init} $Expr{cond}; $Name{i} -= 1) $Stmt{b} }
  end;

global transLoop::s:Strategy =
  rule on Stmt of
  -- Restore increment operator on loops that are otherwise-normal
  | ableC_Stmt {
      for ($BaseTypeExpr{t} $Name{i1} = 0; $Name{i2} < $Expr{n}; $Name{i3} += 1) $Stmt{b}
    } when i1.name == i2.name && i1.name == i3.name ->
    ableC_Stmt {
      for ($BaseTypeExpr{t} $Name{i1} = 0; $Name{i2} < $Expr{n}; $Name{i3}++) $Stmt{b}
    }
  
  -- Normalize loops with nonstandard initial or step values
  | ableC_Stmt {
      for ($BaseTypeExpr{t} $Name{i1} = $Expr{initial}; $Name{i2} < $Expr{limit}; $Name{i3} += $Expr{step})
        $Stmt{b}
    } when i1.name == i2.name && i1.name == i3.name && isSimple(initial) && isSimple(step) ->
      let newName::String = s"_iter_${i1.name}_${toString(genInt())}"
      in ableC_Stmt {
        for ($BaseTypeExpr{t} $Name{i1} = 0; $Name{i2} < ($Expr{limit} - $Expr{initial}) / $Expr{step}; $Name{i3}++) {
          typeof($Name{i1}) $name{newName} = $Expr{initial} + $Name{i1} * $Expr{step};
          $Stmt{rewriteWith(rename(i1.name, newName), b).fromJust}
        }
      }
      end
  
  -- Normalize "backwards" loops, possibly with with nonstandard initial or step values
  | ableC_Stmt {
      for ($BaseTypeExpr{t} $Name{i1} = $Expr{initial}; $Name{i2} >= $Expr{limit}; $Name{i3} -= $Expr{step})
        $Stmt{b}
    } when i1.name == i2.name && i1.name == i3.name && isSimple(initial) && isSimple(step) ->
      let newName::String = s"_iter_${i1.name}_${toString(genInt())}"
      in ableC_Stmt {
        for ($BaseTypeExpr{t} $Name{i1} = 0; $Name{i2} < ($Expr{initial} - $Expr{limit} + 1) / $Expr{step}; $Name{i3}++) {
          typeof($Name{i1}) $name{newName} = $Expr{initial} - $Name{i1} * $Expr{step};
          $Stmt{rewriteWith(rename(i1.name, newName), b).fromJust}
        }
      }
      end
  end;

global normalizeLoops::s:Strategy =
  s:bottomUp(s:try(simplifyLoopExprs <* s:repeat(preprocessLoop))) <*
  s:topDown(s:try(transLoop <* simplifyLoopExprs));

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
        for ($BaseTypeExpr{t} $Name{i1} = 0; $Name{i2} < $Expr{n}; $Name{i3}++)
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
  
  ivs.forIterStmtBody = stmtIterStmt(body);
  forwards to ivs.forIterStmtTrans.hostTrans;
}

synthesized attribute iterDefs::[Def];
synthesized attribute hostTrans::Stmt;

nonterminal IterStmt with pp, errors, defs, iterDefs, hostTrans, env, returnType;

abstract production nullIterStmt
top::IterStmt ::= 
{
  top.pp = notext();
  top.errors := [];
  top.defs := [];
  top.iterDefs = [];
  top.hostTrans = nullStmt();
}

abstract production seqIterStmt
top::IterStmt ::= h::IterStmt t::IterStmt
{
  top.pp = ppConcat([ h.pp, line(), t.pp ]);
  top.errors := h.errors ++ t.errors;
  top.defs := h.defs ++ t.defs;
  top.iterDefs = h.iterDefs ++ t.iterDefs;
  top.hostTrans = seqStmt(h.hostTrans, t.hostTrans);
  
  t.env = addEnv(h.defs, h.env);
}

abstract production compoundIterStmt
top::IterStmt ::= is::IterStmt
{
  top.pp = braces(nestlines(2, is.pp));
  top.errors := is.errors;
  top.defs := [];
  top.iterDefs = is.iterDefs;
  top.hostTrans = compoundStmt(is.hostTrans);
  
  is.env = openScopeEnv(top.env);
}

abstract production stmtIterStmt
top::IterStmt ::= s::Stmt
{
  top.pp = braces(braces(nestlines(2, s.pp)));
  top.errors := s.errors;
  top.defs := s.defs;
  top.iterDefs = [];
  top.hostTrans = s;
}

abstract production condIterStmt
top::IterStmt ::= cond::Expr th::IterStmt el::IterStmt
{
  top.pp = pp"if (${cond.pp})${nestlines(2, th.pp)} else ${nestlines(2, el.pp)}";
  top.errors := cond.errors ++ th.errors ++ el.errors;
  
  top.defs := th.defs ++ el.defs;
  top.iterDefs = th.iterDefs ++ el.iterDefs;
  top.hostTrans = ifStmt(cond, th.hostTrans, el.hostTrans);
}

abstract production forIterStmt
top::IterStmt ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr body::IterStmt
{
  top.pp = pp"for (${ppConcat([bty.pp, space(), mty.lpp, n.pp, mty.rpp])} : ${cutoff.pp}) ${braces(nestlines(2, body.pp))}";
  top.errors := bty.errors ++ n.valueRedeclarationCheckNoCompatible ++ d.errors ++ cutoff.errors ++ body.errors;
  
  production d::Declarator =
    declarator(
      n, mty, nilAttribute(),
      justInitializer(exprInitializer(ableC_Expr {0})));
  d.env = openScopeEnv(top.env);
  d.baseType = bty.typerep;
  d.typeModifierIn = bty.typeModifier;
  d.isTopLevel = false;
  d.isTypedef = false;
  d.givenStorageClasses = nilStorageClass();
  d.givenAttributes = nilAttribute();
  d.returnType = top.returnType;
  
  top.defs := [];
  top.iterDefs = valueDef(n.name, declaratorValueItem(d)) :: body.iterDefs;
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
  top.errors := bty.errors ++ n.valueRedeclarationCheckNoCompatible ++ d.errors ++ cutoff.errors ++ body.errors;
  
  production d::Declarator = declarator(n, mty, nilAttribute(), nothingInitializer());
  d.env = openScopeEnv(top.env);
  d.baseType = bty.typerep;
  d.typeModifierIn = bty.typeModifier;
  d.isTopLevel = false;
  d.isTypedef = false;
  d.givenStorageClasses = nilStorageClass();
  d.givenAttributes = nilAttribute();
  d.returnType = top.returnType;
  
  top.defs := [];
  top.iterDefs = body.iterDefs;
  
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
  top.errors := bty.errors ++ n.valueRedeclarationCheckNoCompatible ++ d.errors ++ cutoff.errors ++ body.errors;
  
  production d::Declarator = declarator(n, mty, nilAttribute(), nothingInitializer());
  d.env = openScopeEnv(top.env);
  d.baseType = bty.typerep;
  d.typeModifierIn = bty.typeModifier;
  d.isTopLevel = false;
  d.isTypedef = false;
  d.givenStorageClasses = nilStorageClass();
  d.givenAttributes = nilAttribute();
  d.returnType = top.returnType;
  
  top.defs := [];
  top.iterDefs = body.iterDefs;
  
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

nonterminal IterVars with pp,errors, iterVarNames, forIterStmtTrans, forIterStmtBody, env, returnType;

abstract production consIterVar
top::IterVars ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr rest::IterVars
{
  top.pp = ppConcat([bty.pp, space(), mty.lpp, n.pp, mty.rpp, text(" : "), cutoff.pp, comma(), space(), rest.pp]);
  top.errors :=
    bty.errors ++ mty.errors ++ cutoff.errors ++
    case cutoff.integerConstantValue of
    | just(n) when n < 1 -> [err(cutoff.location, "Split loop size must be >= 1")]
    | _ -> []
    end ++
    rest.errors;
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
      name("_iter_var_" ++ toString(genInt()), location=builtin),
      cutoff, rest);
}

abstract production nilIterVar
top::IterVars ::= 
{
  top.pp = notext();
  top.errors := [];
  top.iterVarNames = [];
  top.forIterStmtTrans = top.forIterStmtBody;
}

synthesized attribute iterVarName::Name;

inherited attribute forIterStmtCutoff::Expr;

nonterminal IterVar with pp, errors, iterVarName, forIterStmtTrans, forIterStmtCutoff, forIterStmtBody, env, returnType;

abstract production iterVar
top::IterVar ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name
{
  top.pp = ppConcat([bty.pp, space(), mty.lpp, n.pp, mty.rpp]);
  top.errors := bty.errors ++ mty.errors;
  top.iterVarName = n;
  top.forIterStmtTrans = forIterStmt(bty, mty, n, top.forIterStmtCutoff, top.forIterStmtBody);
  
  bty.givenRefId = nothing();
  
  mty.baseType = bty.typerep;
  mty.typeModifierIn = bty.typeModifier;
}
