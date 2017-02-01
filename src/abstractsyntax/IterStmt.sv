grammar edu:umn:cs:melt:exts:ableC:halide:src:abstractsyntax;

imports silver:langutil;
imports silver:langutil:pp with implode as ppImplode;

imports edu:umn:cs:melt:ableC:abstractsyntax;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction;
imports edu:umn:cs:melt:ableC:abstractsyntax:env;

global builtin::Location = builtinLoc("halide");

abstract production iterateStmt
top::Stmt ::= is::IterStmt t::Transformation
{
  --top.pp := 
  top.errors :=
    if !null(is.errors ++ t.errors)
    then is.errors ++ t.errors
    else forward.errors;
    
  t.env = addEnv(is.defs, emptyEnv()); -- Env for transformation consists of only the transformable loop variables
  
  t.iterStmtIn = is;
  forwards to t.iterStmtOut.hostTrans;
}

synthesized attribute hostTrans::Stmt;

nonterminal IterStmt with pp, errors, defs, hostTrans, env, returnType;

abstract production nullIterStmt
top::IterStmt ::= 
{
  top.pp = notext();
  top.errors := [];
  top.defs = [];
  top.hostTrans = nullStmt();
}

abstract production seqIterStmt
top::IterStmt ::= h::IterStmt t::IterStmt
{
  top.pp = concat([ h.pp, line(), t.pp ]);
  top.errors := h.errors ++ t.errors;
  top.defs = h.defs ++ t.defs;
  top.hostTrans = seqStmt(h.hostTrans, t.hostTrans);
}

abstract production compoundIterStmt
top::IterStmt ::= s::IterStmt
{
  top.pp = braces(nestlines(2, s.pp));
  forwards to s; -- No special env
}

abstract production exprIterStmt
top::IterStmt ::= e::Expr
{
  top.pp = cat(e.pp, semi());
  top.errors := e.errors;
  top.defs = [];
  top.hostTrans = exprStmt(e);
}

abstract production stmtIterStmt
top::IterStmt ::= s::Stmt
{
  top.pp = braces(braces(nestlines(2, s.pp)));
  top.errors := s.errors;
  top.defs = [];
  top.hostTrans = s;
}

abstract production forIterStmt
top::IterStmt ::= bty::BaseTypeExpr n::Name mty::TypeModifierExpr cutoff::Expr body::IterStmt
{
  top.pp = pp"for (${concat([bty.pp, mty.lpp, n.pp, mty.rpp])} : ${cutoff.pp}) ${body.pp}";
  top.errors := bty.errors ++ d.errors ++ cutoff.errors ++ body.errors;
  
  production d::Declarator = declarator(n, mty, [], nothingInitializer());
  d.env = top.env;
  d.baseType = bty.typerep;
  d.isTopLevel = false;
  d.isTypedef = false;
  
  top.defs = [valueDef(n.name, declaratorValueItem(d))];
  top.hostTrans =
    seqStmt(
      declStmt( 
        variableDecls(
          [],[],
          bty,
          consDeclarator(d, nilDeclarator()))),
      forStmt(
        justExpr(
          binaryOpExpr(
            declRefExpr(n, location=builtin),
            assignOp(eqOp(location=builtin), location=builtin),
            mkIntExpr("0", builtin),
            location=builtin)),
        justExpr(
          binaryOpExpr(
            declRefExpr(n, location=builtin),
            compareOp(ltOp(location=builtin), location=builtin),
            cutoff,
            location=builtin)),
        justExpr(
          unaryOpExpr(
            postIncOp(location=builtin),
            declRefExpr(n, location=builtin),
            location=builtin)),
        body.hostTrans));
  
  body.env = addEnv(d.defs, top.env);
}

abstract production constForIterStmt
top::IterStmt ::= bty::BaseTypeExpr n::Name mty::TypeModifierExpr cutoff::Integer unsigned::Boolean suffix::IntSuffix body::IterStmt
{
  forwards to
    forIterStmt(
      bty, n, mty,
      realConstant(
        integerConstant(toString(cutoff), unsigned, suffix, location=builtin),
        location=builtin),
      body);
}

abstract production multiForIterStmt
top::IterStmt ::= ivs::IterVars body::IterStmt
{
  top.pp = pp"for (${ivs.pp}) ${body.pp}";
  
  ivs.forIterStmtBody = body;
  forwards to ivs.forIterStmtTrans;
}

synthesized attribute iterVarNames::[Name];

synthesized attribute forIterStmtTrans::IterStmt;
inherited attribute forIterStmtBody::IterStmt;

nonterminal IterVars with pp, iterVarNames, forIterStmtTrans, forIterStmtBody;

abstract production consIterVar
top::IterVars ::= bty::BaseTypeExpr n::Name mty::TypeModifierExpr cutoff::Expr t::IterVars
{
  --top.pp =
  top.iterVarNames = n :: t.iterVarNames;
  
  top.forIterStmtTrans = forIterStmt(bty, n, mty, cutoff, t.forIterStmtTrans);
  t.forIterStmtBody = top.forIterStmtBody;
}

{-

    case cutoff of
      realConstant(integerConstant(num, unsigned, suffix)) ->
        constForIterStmt(bt, d, toInt(num), unsigned, suffix, t.forIterStmtTrans)
    | _ -> forIterStmt(bt, d, cutoff, t.forIterStmtTrans)
    end;
-}

abstract production consAnonIterVar
top::IterVars ::= cutoff::Expr t::IterVars
{
  --top.pp =
  forwards to
    consIterVar(
      directTypeExpr(cutoff.typerep),
      name("_iter_var_" ++ toString(genInt()), location=builtin),
      baseTypeExpr(),
      cutoff, t);
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

nonterminal IterVar with pp, iterVarName, forIterStmtTrans, forIterStmtCutoff, forIterStmtBody;

abstract production iterVar
top::IterVar ::= bty::BaseTypeExpr n::Name mty::TypeModifierExpr
{
  --top.pp =
  top.iterVarName = n;
  top.forIterStmtTrans = forIterStmt(bty, n, mty, top.forIterStmtCutoff, top.forIterStmtBody);
}


