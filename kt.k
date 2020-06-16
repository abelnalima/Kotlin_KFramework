module KT-SYNTAX
    import DOMAINS

    syntax Fun ::= "fun" "main" "(" ")" "{" Block "}"

    syntax Skip ::= "Skip"

    syntax Block ::= "{" Stmt "}" | Stmt

    syntax Stmt ::= Skip
                | VarDeclaration
                | Assigner
                | AExp
                //| BExp
                //| SExp

    syntax VarType ::= "Int" 
                    | "Boolean" 
                    | "String"

    syntax VarMod ::= "var" | "val"

    syntax VarDeclaration ::= VarMod Ids "Int"
                        | VarMod Ids "Boolean"
                        | VarMod Ids "String"
                        //| VarMod Ids VarType

    syntax Ids ::= List{Id, ","}

    syntax Assigner ::= VarDeclaration "=" AExp
                    | VarDeclaration "=" BExp
                    | VarDeclaration "=" SExp

    syntax AExp ::= Int

    syntax BExp ::= Bool

    syntax SExp ::= String

    /* REWRITE RULES */

    rule Skip => .

    rule fun main() {B:Block} => B [structural]

    rule var .Ids Int => Skip
    rule var .Ids Boolean => Skip
    rule var .Ids String => Skip
    rule var .Ids Int = _:Int => Skip
    rule var .Ids Boolean = _:Bool => Skip
    rule var .Ids String = _:String => Skip
    /*rule Vm:VarMod .Ids T:VarType => Skip*/

    /* ARITHMETHIC EXPRESSIONS RULES */


    /* MEMORY ALLOCATION RULES */

    rule <k> var I:Id Int => Skip ... </k> //Tipo Int com auto valor
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> 0 </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> var I:Id Boolean => Skip ... </k> //Tipo Boolean com auto valor
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> false </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> var I:Id String => Skip ... </k> //Tipo String com auto valor
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> " " </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> var (I:Id, Xs:Ids) Int => var Xs Int ... </k> //Tipo Int com auto valor [Mult]
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> 0 </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> var I:Id Int = V:Int => Skip ...  </k> //Tipo Int com valor informado
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> var I:Id Boolean = V:Bool => Skip ...  </k> //Tipo Boolean com valor informado
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> var I:Id String = V:String => Skip ...  </k> //Tipo String com valor informado
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> var (I:Id, Xs:Ids) Int = V:Int => var Xs Int = V ... </k> //Tipo Int com valor informado [Mult]
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> var (I:Id, Xs:Ids) Boolean = V:Bool => var Xs Boolean = V ... </k> //Tipo Boolean com valor informado [Mult]
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> var (I:Id, Xs:Ids) String = V:String => var Xs Int = V ... </k> //Tipo String com valor informado [Mult]
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>

    /*rule <k> Vm:VarMod I:Id T:VarType => Skip ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> 0 </store>
        <loc> L:Int => L +Int 1 </loc>*/

    /* CONFIGURATIONS */

    configuration <T> 
        <k> $PGM:Fun </k>
        <env> .Map </env>
        <store> .Map </store>
        <loc> 1 </loc>
     
    </T>

endmodule

module KT

    import DOMAINS
    import KT-SYNTAX
    syntax KResult ::= Int | Bool

endmodule