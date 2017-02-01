grammar edu:umn:cs:melt:exts:ableC:halide:src:abstractsyntax;

inherited attribute iterStmtIn::IterStmt;
synthesized attribute iterStmtOut::IterStmt;
synthesized attribute envOut::Decorated Env;

nonterminal Transformation with pp, errors, iterStmtIn, iterStmtOut, env, envOut;

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
}

abstract production splitTransformation
top::Transformation ::= n::Name outerBT::BaseTypeExpr outerD::Declarator ivs::IterVars
{
  --top.pp =
  top.errors := n.valueLookupCheck; -- ++ iterStmt.errors;
 
  local iterStmt::IterStmt = top.iterStmtIn;
  iterStmt.env = top.env;
  iterStmt.target = n.name;
  -- TODO: other params
  
  top.iterStmtOut = iterStmt.splitTrans;
  top.envOut = addEnv(iterStmt.defs, emptyEnv());
}

abstract production anonSplitTransformation
top::Transformation ::= n::Name ivs::IterVars
{
  forwards to
    splitTransformation(
      n,
      directTypeExpr(n.valueItem.typerep),
      declarator(
        name("_iter_var_" ++ toString(genInt()), location=builtin),
        baseTypeExpr(),
        [], nothingInitializer()),
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

aspect production exprIterStmt
top::IterStmt ::= e::Expr
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
      body);
  
  local iterVar::IterVar = top.newIterVar;
  iterVar.forIterStmtCutoff = cutoff;
  iterVar.forIterStmtBody = iterVars.forIterStmtTrans;

  top.splitTrans = 
    if n.name == top.target
    then iterVar.forIterStmtTrans
    else forIterStmt(bty, n, mty, cutoff, body.splitTrans);
}

synthesized attribute splitIndexTrans::Expr occurs on IterVars;
inherited attribute splitIndexTransIn::Expr occurs on IterVars;

aspect production consIterVar
top::IterVars ::= bty::BaseTypeExpr n::Name mty::TypeModifierExpr cutoff::Expr t::IterVars
{
  top.splitIndexTrans = t.splitIndexTrans;
  t.splitIndexTransIn =
    mkAdd(
      binaryOpExpr(
        top.splitIndexTransIn,
        numOp(mulOp(location=builtin), location=builtin),
        cutoff,
        location=builtin),
      declRefExpr(n, location=builtin),
      builtin);
        
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
}