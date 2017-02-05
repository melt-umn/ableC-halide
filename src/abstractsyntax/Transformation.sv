grammar edu:umn:cs:melt:exts:ableC:halide:src:abstractsyntax;

inherited attribute iterStmtIn::IterStmt;
synthesized attribute iterStmtOut::IterStmt;

nonterminal Transformation with location, pp, errors, iterStmtIn, iterStmtOut, env, returnType;

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
  top.pp = concat([h.pp, line(), t.pp]);
  top.errors := if !null(h.errors) then h.errors else t.errors;
  
  h.iterStmtIn = top.iterStmtIn;
  t.iterStmtIn = h.iterStmtOut;
  top.iterStmtOut = t.iterStmtOut;
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
  
  n.env = addEnv(iterStmt.iterDefs, emptyEnv()); -- Env for name lookup consists of only the transformable loop variables
 
  local iterStmt::IterStmt = top.iterStmtIn;
  iterStmt.target = n;
  iterStmt.newIterVar = iv;
  iterStmt.newIterVars = ivs;
  iterStmt.env = top.env;
  iterStmt.returnType = top.returnType;
  
  top.iterStmtOut = iterStmt.splitTrans;
}

abstract production anonSplitTransformation
top::Transformation ::= n::Name ivs::IterVars
{
  local iterStmt::IterStmt = top.iterStmtIn;
  iterStmt.env = top.env;
  iterStmt.returnType = top.returnType;
  
  n.env = addEnv(iterStmt.iterDefs, emptyEnv());
  
  forwards to
    splitTransformation(
      n,
      iterVar(
        directTypeExpr(n.valueItem.typerep),
        baseTypeExpr(),
        name("_iter_var_" ++ toString(genInt()), location=builtin)),
      ivs,
      location=top.location);
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
  
  ns.env = addEnv(iterStmt.iterDefs, emptyEnv());
 
  local iterStmt::IterStmt = top.iterStmtIn;
  iterStmt.targets = ns;
  iterStmt.env = top.env;
  iterStmt.returnType = top.returnType;
  
  top.iterStmtOut = iterStmt.reorderTrans;
}

abstract production tileTransformation
top::Transformation ::= ns::Names sizes::[Integer]
{
  top.pp =
    cat(
      pp"tile ${ppImplode(pp", ", ns.pps)} ",
      pp"into (${text(implode(", ", map(\ i::Integer -> toString(i), sizes)))});");
  top.errors :=
     (if ns.count != length(sizes)
      then [err(top.location, s"Incorrect tile dimension: Expected ${toString(ns.count)}, got ${toString(length(sizes))}")]
      else []) ++
     if !null(iterStmt.errors)
     then iterStmt.errors
     else if !null(ns.loopLookupChecks)
     then ns.loopLookupChecks
     else if !null(iterStmt.reorderErrors)
     then iterStmt.reorderErrors
     else forward.errors;
  
  ns.tileSize = sizes;
  ns.tileOuterNamesIn = ns.tileOuterNames;
  ns.env = addEnv(iterStmt.iterDefs, emptyEnv());
  
  -- Decorate iterStmtIn to check loops are contiguous before splitting loops and reordering via forward
  local iterStmt::IterStmt = top.iterStmtIn;
  iterStmt.targets = ns;
  iterStmt.env = top.env;
  iterStmt.returnType = top.returnType;
  
  forwards to
    seqTransformation(
      ns.tileTransformation,
      reorderTransformation(ns.tileNames, location=builtin),
      location=builtin);
}

synthesized attribute names::[String];
synthesized attribute loopLookupChecks :: [Message];

nonterminal Names with pps, names, count, loopLookupChecks, env;

abstract production consName
top::Names ::= h::Name t::Names
{
  top.pps = h.pp :: t.pps;
  top.names = h.name :: t.names;
  top.count = t.count + 1;
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
  top.count = 0;
  top.loopLookupChecks = [];
}

-- Parameter attributes for various transformations
autocopy attribute target::Name occurs on IterStmt;
autocopy attribute targets::Names occurs on IterStmt;
autocopy attribute newIterVar::IterVar occurs on IterStmt;
autocopy attribute newIterVars::IterVars occurs on IterStmt;

-- Functor attributes that perform various transformations
synthesized attribute splitTrans::IterStmt occurs on IterStmt;
synthesized attribute insertTrans::IterStmt occurs on IterStmt;
synthesized attribute reorderTrans::IterStmt occurs on IterStmt, Names;

-- Aspects for base cases for various transformations
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
}

aspect production seqIterStmt
top::IterStmt ::= h::IterStmt t::IterStmt
{
  propagate splitTrans, reorderTrans;
  top.reorderErrors = h.reorderErrors ++ t.reorderErrors;
}

aspect production compoundIterStmt
top::IterStmt ::= is::IterStmt
{
  propagate splitTrans, reorderTrans;
  top.reorderErrors = is.reorderErrors;
}

aspect production stmtIterStmt
top::IterStmt ::= s::Stmt
{
  propagate splitTrans, reorderTrans;
  top.reorderErrors = [];
}

aspect production condIterStmt
top::IterStmt ::= cond::Expr th::IterStmt el::IterStmt
{
  propagate splitTrans, reorderTrans;
  top.reorderErrors = th.reorderErrors ++ el.reorderErrors;
}

-- insertTrans
autocopy attribute insertedTransFn::(IterStmt ::= IterStmt) occurs on IterStmt;

aspect production forIterStmt
top::IterStmt ::= bty::BaseTypeExpr n::Name mty::TypeModifierExpr cutoff::Expr body::IterStmt
{
  propagate insertTrans;
}

-- splitTrans
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

aspect production nilIterVar
top::IterVars ::= 
{
  top.splitIndexTrans = top.splitIndexTransIn;
  top.outerCutoffTrans = mkIntConst(1, builtin);
}

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
                  justInitializer(exprInitializer(splitIterVars.splitIndexTrans))), 
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
  
  local splitIterVars::IterVars = top.newIterVars;
  splitIterVars.splitIndexTransIn =
    declRefExpr(spliIterVar.iterVarName, location=builtin);
  splitIterVars.forIterStmtBody = splitTransBody.insertTrans;
  splitIterVars.env = top.env;
  splitIterVars.returnType = top.returnType;
  
  local spliIterVar::IterVar = top.newIterVar;
  spliIterVar.forIterStmtCutoff = -- Calculate ceil(cutoff/product of split indices)
    mkAdd(
      mkIntConst(1, builtin),
      binaryOpExpr(
        binaryOpExpr(
          cutoff,
          numOp(subOp(location=builtin), location=builtin),
          mkIntConst(1, builtin),
          location=builtin),
        numOp(divOp(location=builtin), location=builtin),
        splitIterVars.outerCutoffTrans,
        location=builtin),
      builtin);
  spliIterVar.forIterStmtBody = splitIterVars.forIterStmtTrans;

  top.splitTrans = 
    if n.name == top.target.name
    then spliIterVar.forIterStmtTrans
    else forIterStmt(bty, n, mty, cutoff, body.splitTrans);
}

-- reorderTrans
autocopy attribute reorderConstructorsIn::[Pair<String (IterStmt ::= IterStmt)>] occurs on Names;
autocopy attribute reorderBaseIterStmtIn::IterStmt occurs on Names;

synthesized attribute reorderConstructors::[Pair<String (IterStmt ::= IterStmt)>] occurs on IterStmt;
synthesized attribute reorderBaseIterStmt::IterStmt occurs on IterStmt;

synthesized attribute reorderErrors::[Message] occurs on IterStmt, Names;

aspect production consName
top::Names ::= h::Name t::Names
{
  local reorderLookupRes::Maybe<(IterStmt ::= IterStmt)> =
    lookupBy(stringEq, h.name, top.reorderConstructorsIn);

  top.reorderErrors =
    case reorderLookupRes of
      just(_) ->
        if containsBy(stringEq, h.name, t.names)
        then [err(h.location, s"Duplicate loop name ${h.name}")]
        else []
    | nothing() -> [err(h.location, s"Loop ${h.name} is not contiguous")]
    end ++ t.reorderErrors;
  
  top.reorderTrans = 
    case reorderLookupRes of
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

aspect production forIterStmt
top::IterStmt ::= bty::BaseTypeExpr n::Name mty::TypeModifierExpr cutoff::Expr body::IterStmt
{
  top.reorderConstructors =
    if containsBy(stringEq, n.name, top.targets.names)
    then pair(n.name, forIterStmt(bty, n, mty, cutoff, _)) :: body.reorderConstructors
    else [];
  
  top.reorderBaseIterStmt =
    if containsBy(stringEq, n.name, top.targets.names)
    then body.reorderBaseIterStmt
    else top;
  
  local reorderTargets::Names = top.targets;
  reorderTargets.reorderConstructorsIn = top.reorderConstructors;
  reorderTargets.reorderBaseIterStmtIn = top.reorderBaseIterStmt;
  
  top.reorderErrors = 
    if containsBy(stringEq, n.name, top.targets.names)
    then reorderTargets.reorderErrors
    else body.reorderErrors;

  top.reorderTrans = 
    if containsBy(stringEq, n.name, top.targets.names)
    then reorderTargets.reorderTrans
    else forIterStmt(bty, n, mty, cutoff, body.reorderTrans);
}

-- tileTrans
autocopy attribute tileSize::[Integer] occurs on Names;
autocopy attribute tileOuterNamesIn::Names occurs on Names;

synthesized attribute tileOuterNames::Names occurs on Names;
synthesized attribute tileNames::Names occurs on Names;
synthesized attribute tileTransformation::Transformation occurs on Names;

aspect production consName
top::Names ::= h::Name t::Names
{
  local outerName::Name = name(h.name ++ "_outer", location=builtin);
  local innerName::Name = name(h.name ++ "_inner", location=builtin);
  
  top.tileOuterNames = consName(outerName, t.tileOuterNames);
  top.tileNames = consName(innerName, t.tileNames);

  top.tileTransformation =
    seqTransformation(
      splitTransformation(
        h,
        iterVar(directTypeExpr(h.valueItem.typerep), baseTypeExpr(), outerName),
        consIterVar(
          directTypeExpr(h.valueItem.typerep),
          baseTypeExpr(),
          innerName,
          mkIntExpr(
            if !null(top.tileSize) -- Avoid crashing if not enough sizes are given
            then toString(head(top.tileSize))
            else "1",
            builtin),
          nilIterVar()),
        location=builtin),
      t.tileTransformation,
      location=builtin);
  
  t.tileSize = tail(top.tileSize);
}

aspect production nilName
top::Names ::= 
{
  top.tileOuterNames = nilName();
  top.tileNames = top.tileOuterNamesIn;
  top.tileTransformation = nullTransformation(location=builtin);
}