grammar edu:umn:cs:melt:exts:ableC:halide:src:abstractsyntax;

inherited attribute iterStmtIn::IterStmt;
synthesized attribute iterStmtOut::IterStmt;
inherited attribute iterEnvIn::Decorated Env;
synthesized attribute iterEnvOut::Decorated Env;

nonterminal Transformation with pp, errors, iterStmtIn, iterStmtOut, iterEnvIn, iterEnvOut, env;

abstract production nullTransformation
top::Transformation ::= 
{
  top.pp = notext();
  top.errors := [];
  top.iterStmtOut = top.iterStmtIn;
}

abstract production seqTransformation
top::Transformation ::= h::Transformation t::Transformation
{
  top.pp = concat([ h.pp, line(), t.pp ]);
  top.errors := h.errors ++ t.errors;
  
  h.iterStmtIn = top.iterStmtIn;
  t.iterStmtIn = h.iterStmtOut;
  top.iterStmtOut = t.iterStmtOut;
  t.iterEnvIn = h.iterEnvOut;
  top.iterEnvOut = t.iterEnvOut;
}

abstract production splitTransformation
top::Transformation ::= n::Name iv::IterVar ivs::IterVars
{
  --top.pp =
  top.errors := n.valueLookupCheck; -- ++ iterStmt.errors;
  
  n.env = top.iterEnvIn;
 
  local iterStmt::IterStmt = top.iterStmtIn;
  iterStmt.env = top.env;
  iterStmt.target = n.name;
  iterStmt.newIterVar = iv;
  iterStmt.newIterVars = ivs;
  
  top.iterStmtOut = iterStmt.splitTrans;
  top.iterEnvOut = addEnv(iterStmt.defs, emptyEnv());
}

abstract production anonSplitTransformation
top::Transformation ::= n::Name ivs::IterVars
{
  n.env = top.iterEnvIn;
  forwards to
    splitTransformation(
      n,
      iterVar(
        directTypeExpr(n.valueItem.typerep),
        baseTypeExpr(),
        name("_iter_var_" ++ toString(genInt()), location=builtin)),
      ivs);
}

-- Parameter attributes for various transformations
autocopy attribute target::String occurs on IterStmt;
autocopy attribute targets::[String] occurs on IterStmt;
autocopy attribute newIterVar::IterVar occurs on IterStmt;
autocopy attribute newIterVars::IterVars occurs on IterStmt;

synthesized attribute splitTrans::IterStmt occurs on IterStmt;

aspect production nullIterStmt
top::IterStmt ::= 
{
  propagate splitTrans;
}

aspect production seqIterStmt
top::IterStmt ::= h::IterStmt t::IterStmt
{
  propagate splitTrans;
}

aspect production stmtIterStmt
top::IterStmt ::= s::Stmt
{
  propagate splitTrans;
}

aspect production forIterStmt
top::IterStmt ::= bty::BaseTypeExpr n::Name mty::TypeModifierExpr cutoff::Expr body::IterStmt
{
  local iterVars::IterVars = top.newIterVars;
  iterVars.splitIndexTransIn =
    declRefExpr(iterVar.iterVarName, location=builtin);
  iterVars.forIterStmtBody =
    seqIterStmt(
      stmtIterStmt(
        declStmt( 
          variableDecls(
            [], [],
            directTypeExpr(d.typerep),
            consDeclarator( 
              declarator(
                n, baseTypeExpr(), [], 
                justInitializer(exprInitializer(iterVars.splitIndexTrans))), 
                nilDeclarator())))),
      condIterStmt(
        binaryOpExpr(
          declRefExpr(n, location=builtin),
          compareOp(ltOp(location=builtin), location=builtin),
          cutoff,
          location=builtin),
        body,
        nullIterStmt()));
  
  local iterVar::IterVar = top.newIterVar;
  iterVar.forIterStmtCutoff =
    binaryOpExpr(
      cutoff,
      numOp(divOp(location=builtin), location=builtin),
      iterVars.outerCutoffTrans,
      location=builtin);
  iterVar.forIterStmtBody = iterVars.forIterStmtTrans;

  top.splitTrans = 
    if n.name == top.target
    then iterVar.forIterStmtTrans
    else forIterStmt(bty, n, mty, cutoff, body.splitTrans);
}

aspect production condIterStmt
top::IterStmt ::= cond::Expr th::IterStmt el::IterStmt
{
  propagate splitTrans;
}

synthesized attribute splitIndexTrans::Expr occurs on IterVars;
inherited attribute splitIndexTransIn::Expr occurs on IterVars;

synthesized attribute outerCutoffTrans::Expr occurs on IterVars;

aspect production consIterVar
top::IterVars ::= bty::BaseTypeExpr mty::TypeModifierExpr n::Name cutoff::Expr rest::IterVars
{
  top.splitIndexTrans = rest.splitIndexTrans;
  rest.splitIndexTransIn =
    mkAdd(
      binaryOpExpr(
        top.splitIndexTransIn,
        numOp(mulOp(location=builtin), location=builtin),
        cutoff,
        location=builtin),
      declRefExpr(n, location=builtin),
      builtin);
  
  top.outerCutoffTrans = 
    binaryOpExpr(
      cutoff,
      numOp(mulOp(location=builtin), location=builtin),
      rest.outerCutoffTrans,
      location=builtin);
}

{-
aspect production consAnonIterVar
top::IterVars ::= cutoff::Expr t::IterVars
{
}
-}

aspect production nilIterVar
top::IterVars ::= 
{
  top.splitIndexTrans = top.splitIndexTransIn;
  top.outerCutoffTrans =
    realConstant(integerConstant("1", true, noIntSuffix(), location=builtin), location=builtin);
}