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
  top.pp = concat([pp"transform ", braces(nestlines(2, is.pp)), pp" by ", braces(nestlines(2, t.pp))]);
  top.errors :=
    {-if !null(is.errors) -- iterStmtIn.errors get checked by every transformation that decorates iterStmtIn
    then is.errors
    else -}if !null(t.errors)
    then t.errors
    else if !null(transResult.errors)
    then transResult.errors
    else forward.errors;
  
  t.iterStmtIn = is;
  
  local transResult::IterStmt = t.iterStmtOut;
  transResult.env = top.env;
  transResult.returnType = top.returnType;
  
  forwards to transResult.hostTrans;
}

synthesized attribute iterDefs::[Def];
synthesized attribute hostTrans::Stmt;

nonterminal IterStmt with pp, errors, defs, iterDefs, hostTrans, env, returnType;

abstract production nullIterStmt
top::IterStmt ::= 
{
  top.pp = notext();
  top.errors := [];
  top.defs = [];
  top.iterDefs = [];
  top.hostTrans = nullStmt();
}

abstract production seqIterStmt
top::IterStmt ::= h::IterStmt t::IterStmt
{
  top.pp = concat([ h.pp, line(), t.pp ]);
  top.errors := h.errors ++ t.errors;
  top.defs = h.defs ++ t.defs;
  top.iterDefs = h.iterDefs ++ t.iterDefs;
  top.hostTrans = seqStmt(h.hostTrans, t.hostTrans);
  
  t.env = addEnv(h.defs, h.env);
}

abstract production compoundIterStmt
top::IterStmt ::= is::IterStmt
{
  top.pp = braces(nestlines(2, is.pp));
  top.errors := is.errors;
  top.defs = [];
  top.iterDefs = is.iterDefs;
  top.hostTrans = compoundStmt(is.hostTrans);
  
  is.env = openScope(top.env);
}

abstract production stmtIterStmt
top::IterStmt ::= s::Stmt
{
  top.pp = braces(braces(nestlines(2, s.pp)));
  top.errors := s.errors;
  top.defs = s.defs;
  top.iterDefs = [];
  top.hostTrans = s;
}

abstract production condIterStmt
top::IterStmt ::= cond::Expr th::IterStmt el::IterStmt
{
  top.pp = pp"if (${cond.pp})${nestlines(2, th.pp)} else ${nestlines(2, el.pp)}";
  top.errors := cond.errors ++ th.errors ++ el.errors;
  
  top.defs = th.defs ++ el.defs;
  top.iterDefs = th.iterDefs ++ el.iterDefs;
  top.hostTrans = ifStmt(cond, th.hostTrans, el.hostTrans);
}

abstract production forIterStmt
top::IterStmt ::= bty::BaseTypeExpr n::Name mty::TypeModifierExpr cutoff::Expr body::IterStmt
{
  top.pp = pp"for (${concat([bty.pp, space(), mty.lpp, n.pp, mty.rpp])} : ${cutoff.pp}) ${braces(nestlines(2, body.pp))}";
  top.errors := bty.errors ++ n.valueRedeclarationCheckNoCompatible ++ d.errors ++ cutoff.errors ++ body.errors;
  
  production d::Declarator = declarator(n, mty, [], nothingInitializer());
  d.env = openScope(top.env);
  d.baseType = bty.typerep;
  d.isTopLevel = false;
  d.isTypedef = false;
  d.givenAttributes = [];
  d.returnType = top.returnType;
  
  top.defs = [];
  top.iterDefs = valueDef(n.name, declaratorValueItem(d)) :: body.iterDefs;
  top.hostTrans =
    compoundStmt(
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
          body.hostTrans)));
  
  body.env = addEnv(d.defs, openScope(top.env));
}

abstract production multiForIterStmt
top::IterStmt ::= ivs::IterVars body::IterStmt
{
  top.pp = pp"for (${ivs.pp}) ${braces(nestlines(2, body.pp))}";
  
  ivs.forIterStmtBody = body;
  forwards to ivs.forIterStmtTrans;
}

synthesized attribute iterVarNames::[Name];

synthesized attribute forIterStmtTrans::IterStmt;
inherited attribute forIterStmtBody::IterStmt;

nonterminal IterVars with pp, errors, iterVarNames, forIterStmtTrans, forIterStmtBody, env, returnType;

abstract production consIterVar
top::IterVars ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr rest::IterVars
{
  top.pp = concat([bty.pp, space(), mty.lpp, n.pp, mty.rpp, text(" : "), cutoff.pp, comma(), space(), rest.pp]);
  top.errors := bty.errors ++ mty.errors ++ cutoff.errors ++ rest.errors;
  top.iterVarNames = n :: rest.iterVarNames;
  
  top.forIterStmtTrans = forIterStmt(bty, n, mty, cutoff, rest.forIterStmtTrans);
  rest.forIterStmtBody = top.forIterStmtBody;
}

{-

    case cutoff of
      realConstant(integerConstant(num, unsigned, suffix)) ->
        constForIterStmt(bt, d, toInt(num), unsigned, suffix, t.forIterStmtTrans)
    | _ -> forIterStmt(bt, d, cutoff, t.forIterStmtTrans)
    end;
-}

abstract production consAnonIterVar
top::IterVars ::= cutoff::Expr rest::IterVars
{
  top.pp = concat([cutoff.pp, comma(), rest.pp]);
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
  top.pp = concat([bty.pp, space(), mty.lpp, n.pp, mty.rpp]);
  top.errors := bty.errors ++ mty.errors;
  top.iterVarName = n;
  top.forIterStmtTrans = forIterStmt(bty, n, mty, top.forIterStmtCutoff, top.forIterStmtBody);
}