grammar edu:umn:cs:melt:exts:ableC:halide:artifacts:silver_compiler;

{- This Silver specification defines the extended verison of Silver
   needed to build this extension.
 -}

import edu:umn:cs:melt:ableC:concretesyntax as cst;
import edu:umn:cs:melt:ableC:drivers:compile;
import silver:compiler:host;

parser svParse::Root {
  silver:compiler:host;
  edu:umn:cs:melt:ableC:silverconstruction;
  edu:umn:cs:melt:ableC:concretesyntax;
}

fun main IO<Integer> ::= args::[String] = cmdLineRun(args, svParse);