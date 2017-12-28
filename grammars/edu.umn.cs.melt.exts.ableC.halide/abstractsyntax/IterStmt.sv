grammar edu:umn:cs:melt:exts:ableC:halide:abstractsyntax;

imports silver:langutil;
imports silver:langutil:pp;

imports edu:umn:cs:melt:ableC:abstractsyntax:host;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction;
imports edu:umn:cs:melt:ableC:abstractsyntax:substitution;
imports edu:umn:cs:melt:ableC:abstractsyntax:env;

global builtin::Location = builtinLoc("halide");

abstract production iterateStmt
top::Stmt ::= is::IterStmt t::Transformation
{
  propagate substituted;
  top.pp =
    ppConcat([pp"transform ", braces(nestlines(2, is.pp)), pp" by ", braces(nestlines(2, t.pp))]);
  top.functionDefs := [];
  
  t.iterStmtIn = is;
  
  local transResult::IterStmt = t.iterStmtOut;
  transResult.env = top.env;
  transResult.returnType = top.returnType;
  
  forwards to
    {-if !null(is.errors) -- iterStmtIn.errors get checked by every transformation that decorates iterStmtIn
    then warnStmt(is.errors)
    else -}if !null(t.errors)
    then warnStmt(t.errors)
    else if !null(transResult.errors)
    then warnStmt(transResult.errors)
    else transResult.hostTrans;
}

synthesized attribute iterDefs::[Def];
synthesized attribute hostTrans::Stmt;

nonterminal IterStmt with pp, substituted<IterStmt>, errors, defs, iterDefs, hostTrans, substitutions, env, returnType;

abstract production nullIterStmt
top::IterStmt ::= 
{
  propagate substituted;
  top.pp = notext();
  top.errors := [];
  top.defs := [];
  top.iterDefs = [];
  top.hostTrans = nullStmt();
}

abstract production seqIterStmt
top::IterStmt ::= h::IterStmt t::IterStmt
{
  propagate substituted;
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
  propagate substituted;
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
  propagate substituted;
  top.pp = braces(braces(nestlines(2, s.pp)));
  top.errors := s.errors;
  top.defs := s.defs;
  top.iterDefs = [];
  top.hostTrans = s;
}

abstract production condIterStmt
top::IterStmt ::= cond::Expr th::IterStmt el::IterStmt
{
  propagate substituted;
  top.pp = pp"if (${cond.pp})${nestlines(2, th.pp)} else ${nestlines(2, el.pp)}";
  top.errors := cond.errors ++ th.errors ++ el.errors;
  
  top.defs := th.defs ++ el.defs;
  top.iterDefs = th.iterDefs ++ el.iterDefs;
  top.hostTrans = ifStmt(cond, th.hostTrans, el.hostTrans);
}

abstract production forIterStmt
top::IterStmt ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr body::IterStmt
{
  propagate substituted;
  top.pp = pp"for (${ppConcat([bty.pp, space(), mty.lpp, n.pp, mty.rpp])} : ${cutoff.pp}) ${braces(nestlines(2, body.pp))}";
  top.errors := bty.errors ++ n.valueRedeclarationCheckNoCompatible ++ d.errors ++ cutoff.errors ++ body.errors;
  
  production d::Declarator = declarator(n, mty, nilAttribute(), nothingInitializer());
  d.env = openScopeEnv(top.env);
  d.baseType = bty.typerep;
  d.typeModifiersIn = bty.typeModifiers;
  d.isTopLevel = false;
  d.isTypedef = false;
  d.givenAttributes = nilAttribute();
  d.returnType = top.returnType;
  
  top.defs := [];
  top.iterDefs = valueDef(n.name, declaratorValueItem(d)) :: body.iterDefs;
  top.hostTrans =
    compoundStmt(
      seqStmt(
        declStmt( 
          variableDecls(
            [], nilAttribute(),
            bty,
            consDeclarator(d, nilDeclarator()))),
        forStmt(
          justExpr(
            eqExpr(
              declRefExpr(n, location=builtin),
              mkIntConst(0, builtin),
              location=builtin)),
          justExpr(
            ltExpr(
              declRefExpr(n, location=builtin),
              cutoff,
              location=builtin)),
          justExpr(
            postIncExpr(
              declRefExpr(n, location=builtin),
              location=builtin)),
          body.hostTrans)));
  
  bty.givenRefId = nothing();
  body.env = addEnv(d.defs, openScopeEnv(top.env));
}

abstract production multiForIterStmt
top::IterStmt ::= ivs::IterVars body::IterStmt
{
  propagate substituted;
  top.pp = pp"for (${ivs.pp}) ${braces(nestlines(2, body.pp))}";
  
  ivs.forIterStmtBody = body;
  forwards to ivs.forIterStmtTrans;
}

abstract production parallelForIterStmt
top::IterStmt ::= numThreads::Maybe<Integer> bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr body::IterStmt
{
  propagate substituted;
  local numThreadsPP::Document =
    case numThreads of
      just(n) -> parens(text(toString(n)))
    | nothing() -> notext()
    end;
  top.pp = pp"for parallel${numThreadsPP} (${ppConcat([bty.pp, space(), mty.lpp, n.pp, mty.rpp])} : ${cutoff.pp}) ${braces(nestlines(2, body.pp))}";
  top.errors := bty.errors ++ n.valueRedeclarationCheckNoCompatible ++ d.errors ++ cutoff.errors ++ body.errors;
  
  production d::Declarator = declarator(n, mty, nilAttribute(), nothingInitializer());
  d.env = openScopeEnv(top.env);
  d.baseType = bty.typerep;
  d.typeModifiersIn = bty.typeModifiers;
  d.isTopLevel = false;
  d.isTypedef = false;
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
            [], nilAttribute(),
            bty,
            consDeclarator(d, nilDeclarator()))),
        case numThreads of
          just(n) -> txtStmt(s"#pragma omp parallel for num_threads(${toString(n)})")
        | nothing() -> txtStmt("#pragma omp parallel for")
        end,
        txtStmt(s"for (${show(80, bty.pp)} ${show(80, head(d.pps))} = 0; ${n.name} < ${show(80, cutoff.pp)}; ${n.name}++)"),
        body.hostTrans]));
  
  bty.givenRefId = nothing();
  
  body.env = addEnv(d.defs, openScopeEnv(top.env));
}

abstract production vectorForIterStmt
top::IterStmt ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr body::IterStmt
{
  propagate substituted;
  top.pp = pp"for vector (${ppConcat([bty.pp, space(), mty.lpp, n.pp, mty.rpp])} : ${cutoff.pp}) ${braces(nestlines(2, body.pp))}";
  top.errors := bty.errors ++ n.valueRedeclarationCheckNoCompatible ++ d.errors ++ cutoff.errors ++ body.errors;
  
  production d::Declarator = declarator(n, mty, nilAttribute(), nothingInitializer());
  d.env = openScopeEnv(top.env);
  d.baseType = bty.typerep;
  d.typeModifiersIn = bty.typeModifiers;
  d.isTopLevel = false;
  d.isTypedef = false;
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
            [], nilAttribute(),
            bty,
            consDeclarator(d, nilDeclarator()))),
        txtStmt("#pragma omp simd"),
        txtStmt(s"for (${show(80, bty.pp)} ${show(80, head(d.pps))} = 0; ${n.name} < ${show(80, cutoff.pp)}; ${n.name}++)"),
        body.hostTrans]));
  
  bty.givenRefId = nothing();
  
  body.env = addEnv(d.defs, openScopeEnv(top.env));
}

synthesized attribute iterVarNames::[Name];

synthesized attribute forIterStmtTrans::IterStmt;
inherited attribute forIterStmtBody::IterStmt;

nonterminal IterVars with pp, substituted<IterVars>, errors, iterVarNames, forIterStmtTrans, forIterStmtBody, substitutions, env, returnType;

abstract production consIterVar
top::IterVars ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr rest::IterVars
{
  propagate substituted;
  top.pp = ppConcat([bty.pp, space(), mty.lpp, n.pp, mty.rpp, text(" : "), cutoff.pp, comma(), space(), rest.pp]);
  top.errors :=
    bty.errors ++ mty.errors ++ cutoff.errors ++
    case cutoff of
      realConstant(integerConstant(num, _, _)) ->
        if toInt(num) < 1
        then [err(cutoff.location, "Split loop size must be >= 1")]
        else []
    | _ -> []
    end ++
    rest.errors;
  top.iterVarNames = n :: rest.iterVarNames;
  
  top.forIterStmtTrans = forIterStmt(bty, mty, n, cutoff, rest.forIterStmtTrans);
  rest.forIterStmtBody = top.forIterStmtBody;
  
  bty.givenRefId = nothing();
  
  mty.baseType = bty.typerep;
  mty.typeModifiersIn = bty.typeModifiers;
}

abstract production consAnonIterVar
top::IterVars ::= cutoff::Expr rest::IterVars
{
  propagate substituted;
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
  propagate substituted;
  top.pp = notext();
  top.errors := [];
  top.iterVarNames = [];
  top.forIterStmtTrans = top.forIterStmtBody;
}

synthesized attribute iterVarName::Name;

inherited attribute forIterStmtCutoff::Expr;

nonterminal IterVar with pp, substituted<IterVar>, errors, iterVarName, forIterStmtTrans, forIterStmtCutoff, forIterStmtBody, substitutions, env, returnType;

abstract production iterVar
top::IterVar ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name
{
  propagate substituted;
  top.pp = ppConcat([bty.pp, space(), mty.lpp, n.pp, mty.rpp]);
  top.errors := bty.errors ++ mty.errors;
  top.iterVarName = n;
  top.forIterStmtTrans = forIterStmt(bty, mty, n, top.forIterStmtCutoff, top.forIterStmtBody);
  
  bty.givenRefId = nothing();
  
  mty.baseType = bty.typerep;
  mty.typeModifiersIn = bty.typeModifiers;
}
