grammar edu:umn:cs:melt:exts:ableC:halide:src:abstractsyntax;

inherited attribute iterStmtIn::IterStmt;
synthesized attribute iterStmtOut::IterStmt;
inherited attribute iterEnvIn::Decorated Env;
synthesized attribute iterEnvOut::Decorated Env;

nonterminal Transformation with pp, errors, iterStmtIn, iterStmtOut, iterEnvIn, iterEnvOut, env, returnType;

abstract production nullTransformation
top::Transformation ::= 
{
  top.pp = notext();
  top.errors := [];
  top.iterStmtOut = top.iterStmtIn;
  top.iterEnvOut = top.iterEnvIn;
}

abstract production seqTransformation
top::Transformation ::= h::Transformation t::Transformation
{
  top.pp = concat([h.pp, line(), t.pp]);
  top.errors := if !null(h.errors) then h.errors else t.errors;
  
  h.iterStmtIn = top.iterStmtIn;
  t.iterStmtIn = h.iterStmtOut;
  top.iterStmtOut = t.iterStmtOut;
  h.iterEnvIn = top.iterEnvIn;
  t.iterEnvIn = h.iterEnvOut;
  top.iterEnvOut = t.iterEnvOut;
}

abstract production splitTransformation
top::Transformation ::= n::Name iv::IterVar ivs::IterVars
{
  top.pp = pp"split ${n.pp} into (${iv.pp}, ${ivs.pp});";
  top.errors :=
     if !null(iterStmt.errors)
     then iterStmt.errors
     else (if !null(n.valueLookupCheck)
           then [err(n.location, "Undeclared loop " ++ n.name)]
           else []) ++ iv.errors ++ ivs.errors;
  
  n.env = top.iterEnvOut;
 
  local iterStmt::IterStmt = top.iterStmtIn;
  iterStmt.target = n;
  iterStmt.newIterVar = iv;
  iterStmt.newIterVars = ivs;
  iterStmt.env = top.env;
  iterStmt.returnType = top.returnType;
  
  top.iterStmtOut = iterStmt.splitTrans;
  top.iterEnvOut = addEnv(iterStmt.iterDefs, emptyEnv());
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

abstract production reorderTransformation
top::Transformation ::= ns::Names
{
  top.pp = pp"reorder ${ppImplode(pp", ", ns.pps)};";
  top.errors :=
     if !null(iterStmt.errors)
     then iterStmt.errors
     else if !null(ns.loopLookupChecks)
     then ns.loopLookupChecks
     else iterStmt.reorderErrors;
  
  ns.env = top.iterEnvOut;
 
  local iterStmt::IterStmt = top.iterStmtIn;
  iterStmt.targets = ns;
  iterStmt.env = top.env;
  iterStmt.returnType = top.returnType;
  
  top.iterStmtOut = iterStmt.reorderTrans;
  top.iterEnvOut = addEnv(iterStmt.iterDefs, emptyEnv());
}

synthesized attribute names::[String];
synthesized attribute loopLookupChecks :: [Message];

nonterminal Names with pps, names, loopLookupChecks, env;

abstract production consName
top::Names ::= h::Name t::Names
{
  top.pps = h.pp :: t.pps;
  top.names = h.name :: t.names;
  top.loopLookupChecks =
    (if !null(h.valueLookupCheck)
     then [err(h.location, "Undeclared loop " ++ h.name)]
     else []) ++ t.loopLookupChecks;
}

abstract production nilName
top::Names ::= 
{
  top.pps = [];
  top.names = [];
  top.loopLookupChecks = [];
}

-- Parameter attributes for various transformations
autocopy attribute target::Name occurs on IterStmt;
autocopy attribute targets::Names occurs on IterStmt;
autocopy attribute newIterVar::IterVar occurs on IterStmt;
autocopy attribute newIterVars::IterVars occurs on IterStmt;

autocopy attribute insertedTransFn::(IterStmt ::= IterStmt) occurs on IterStmt;

-- Helper attributes that perform analysies for transformations
synthesized attribute reorderConstructors::[Pair<String (IterStmt ::= IterStmt)>] occurs on IterStmt;
synthesized attribute reorderBaseIterStmt::IterStmt occurs on IterStmt;

synthesized attribute reorderErrors::[Message] occurs on IterStmt, Names;

synthesized attribute isLoop::Boolean occurs on IterStmt;

-- Functor attributes that perform various transformations
synthesized attribute splitTrans::IterStmt occurs on IterStmt;
synthesized attribute insertTrans::IterStmt occurs on IterStmt;
synthesized attribute reorderTrans::IterStmt occurs on IterStmt, Names;

aspect default production
top::IterStmt ::= 
{
  top.insertTrans = top.insertedTransFn(top);
  top.reorderConstructors = [];
  top.reorderBaseIterStmt = top;
}

aspect production nullIterStmt
top::IterStmt ::= 
{
  propagate splitTrans, reorderTrans;
  top.reorderErrors = [];
  top.isLoop = false;
}

aspect production seqIterStmt
top::IterStmt ::= h::IterStmt t::IterStmt
{
  propagate splitTrans, reorderTrans;
  top.reorderErrors = h.reorderErrors ++ t.reorderErrors;
  top.isLoop = false;
}

aspect production compoundIterStmt
top::IterStmt ::= is::IterStmt
{
  propagate splitTrans, reorderTrans;
  top.reorderErrors = is.reorderErrors;
  top.isLoop = is.isLoop;
}

aspect production stmtIterStmt
top::IterStmt ::= s::Stmt
{
  propagate splitTrans, reorderTrans;
  top.reorderErrors = [];
  top.isLoop = false;
}

aspect production condIterStmt
top::IterStmt ::= cond::Expr th::IterStmt el::IterStmt
{
  propagate splitTrans, reorderTrans;
  top.reorderErrors = th.reorderErrors ++ el.reorderErrors;
  top.isLoop = false;
}

-- insertTrans
aspect production forIterStmt
top::IterStmt ::= bty::BaseTypeExpr n::Name mty::TypeModifierExpr cutoff::Expr body::IterStmt
{
  propagate insertTrans;
}

-- splitTrans
aspect production forIterStmt
top::IterStmt ::= bty::BaseTypeExpr n::Name mty::TypeModifierExpr cutoff::Expr body::IterStmt
{
  local splitTransBody::IterStmt = body;
  splitTransBody.insertedTransFn =
    \ innerBody::IterStmt ->
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
          innerBody,
          nullIterStmt()));
  splitTransBody.env = top.env;
  splitTransBody.returnType = top.returnType;
  
  local iterVars::IterVars = top.newIterVars;
  iterVars.splitIndexTransIn =
    declRefExpr(iterVar.iterVarName, location=builtin);
  iterVars.forIterStmtBody = splitTransBody.insertTrans;
  iterVars.env = top.env;
  iterVars.returnType = top.returnType;
  
  local iterVar::IterVar = top.newIterVar;
  iterVar.forIterStmtCutoff = -- Calculate ceil(cutoff/product of split indices)
    mkAdd(
      mkIntConst(1, builtin),
      binaryOpExpr(
        binaryOpExpr(
          cutoff,
          numOp(subOp(location=builtin), location=builtin),
          mkIntConst(1, builtin),
          location=builtin),
        numOp(divOp(location=builtin), location=builtin),
        iterVars.outerCutoffTrans,
        location=builtin),
      builtin);
  iterVar.forIterStmtBody = iterVars.forIterStmtTrans;

  top.splitTrans = 
    if n.name == top.target.name
    then iterVar.forIterStmtTrans
    else forIterStmt(bty, n, mty, cutoff, body.splitTrans);
}

-- reorderTrans
aspect production forIterStmt
top::IterStmt ::= bty::BaseTypeExpr n::Name mty::TypeModifierExpr cutoff::Expr body::IterStmt
{
  top.isLoop = true;
  top.reorderConstructors =
    if containsBy(stringEq, n.name, top.targets.names)
    then pair(n.name, forIterStmt(bty, n, mty, cutoff, _)) :: body.reorderConstructors
    else [];
  
  top.reorderBaseIterStmt =
    if containsBy(stringEq, n.name, top.targets.names)
    then body.reorderBaseIterStmt
    else top;
  
  local targets::Names = top.targets;
  targets.reorderConstructorsIn = top.reorderConstructors;
  targets.reorderBaseIterStmtIn = top.reorderBaseIterStmt;
  
  top.reorderErrors = 
    if containsBy(stringEq, n.name, top.targets.names)
    then targets.reorderErrors
    else body.reorderErrors;

  top.reorderTrans = 
    if containsBy(stringEq, n.name, top.targets.names)
    then targets.reorderTrans
    else forIterStmt(bty, n, mty, cutoff, body.reorderTrans);
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
  top.outerCutoffTrans = mkIntConst(1, builtin);
}

autocopy attribute reorderConstructorsIn::[Pair<String (IterStmt ::= IterStmt)>] occurs on Names;
autocopy attribute reorderBaseIterStmtIn::IterStmt occurs on Names;

aspect production consName
top::Names ::= h::Name t::Names
{
  local lookupRes::Maybe<(IterStmt ::= IterStmt)> =
    lookupBy(stringEq, h.name, top.reorderConstructorsIn);

  top.reorderErrors =
    case lookupRes of
      just(_) ->
        if containsBy(stringEq, h.name, t.names)
        then [err(h.location, s"Duplicate reordered loop ${h.name}")]
        else []
    | nothing() -> [err(h.location, s"Loop ${h.name} cannot be reordered- ${hackUnparse(top.reorderConstructorsIn)}")]
    end ++ t.reorderErrors;
  
  top.reorderTrans = 
    case lookupRes of
      just(fn) -> fn(t.reorderTrans)
    | nothing() -> t.reorderTrans
    end;
}

aspect production nilName
top::Names ::= 
{
  top.reorderErrors = [];
  top.reorderTrans = top.reorderBaseIterStmtIn;
}