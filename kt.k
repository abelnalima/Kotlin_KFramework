module KT-SYNTAX
    import DOMAINS

    syntax Fun ::= "fun" "main" "(" ")" "{" Block "}"

    syntax Skip ::= "Skip"

    syntax Block ::= "{" Stmt "}" | Stmt

    syntax Stmt ::= Skip
                | Stmt Stmt [left]
                | VarDeclaration
                | Assigner
                | IdAssigner
                | IfStmt
                | AExp
                | AExpMod
                | BExp
                | SExp

    syntax VarType ::= "Int" 
                    | "Boolean" 
                    | "String"

    syntax VarMod ::= "var" | "val"

    syntax VarDeclaration ::= VarMod Ids "Int"
                        | VarMod Ids "Boolean"
                        | VarMod Ids "String"
                        //| VarMod Ids VarType

    //syntax ValueType ::= Int | Bool | String //| Id

    syntax Ids ::= List{Id, ","}

    syntax Assigner ::= VarDeclaration "=" AExp [strict(2)]
                    | VarDeclaration "=" BExp [strict(2)]
                    | VarDeclaration "=" SExp [strict(2)]

    syntax IdAssigner ::= Id "=" AExp [strict(2)]
                    | Id "=" BExp [strict(2)]
                    | Id "=" SExp [strict(2)]
                    //| Id "=" ValueType

    syntax AExp ::= Int
                | Id
                > left: AExp "*" AExp [seqstrict]
                > left: AExp "/" AExp [seqstrict]
                | AExp "+" AExp [seqstrict]
                | AExp "-" AExp [seqstrict]
                | "(" AExp ")" [bracket]

    syntax AExpMod ::= Id "++"
                | Id "--"

    syntax BExp ::= Bool
                | Id
                | AExp ">" AExp [strict]
                | AExp "<" AExp [strict]
                | AExp ">=" AExp [strict]
                | AExp "<=" AExp [strict]
                | AExp "==" AExp [strict]
                > "!" BExp [seqstrict, left]
                > left: BExp "&&" BExp [strict]
                | BExp "||" BExp [strict, left]
                | "(" BExp ")" [bracket]

    syntax SExp ::= String
                | Id
                | SExp "+" SExp

    syntax IfStmt ::= "if" "(" BExp ")" Block [strict(1)]
                | "if" "(" BExp ")" Block ElseIfStmt [strict(1)]

    syntax ElseIfStmt ::= "else if" "(" BExp ")" Block
                    | "else if" "(" BExp ")" Block ElseIfStmt
                    | "else" Block

    /* REWRITE RULES */

    rule Skip => .

    rule fun main() {B:Block} => B [structural]

    rule S1:Stmt S2:Stmt => S1 ~> S2 [structural]

    //rule I1:Id = I2:Id => I2 ~> I1 = I2

    rule V:VarMod .Ids Int => Skip
    rule V:VarMod .Ids Boolean => Skip
    rule V:VarMod .Ids String => Skip
    rule V:VarMod .Ids Int = _:Int => Skip
    rule V:VarMod .Ids Boolean = _:Bool => Skip
    rule V:VarMod .Ids String = _:String => Skip
    //rule Vm:VarMod .Ids T:VarType => Skip

    rule if (true) { S:Stmt } => S
    rule if (false) { _ } => Skip
    rule if (true) { S:Stmt } Sif:ElseIfStmt => S
    rule if (false) { _ } S:ElseIfStmt => S
    rule else if (E:BExp) { S1:Stmt } S2:ElseIfStmt => if (E) { S1 } S2
    rule else if (E:BExp) { S:Stmt } => if (E) { S }
    rule else { S:Stmt } => S
    rule if (true) { S:Stmt } else _ => S
    rule if (false) { _ } else { S:Stmt } => S

    /* ARITHMETHIC EXPRESSIONS RULES */

    rule I1:Int + I2:Int => I1 +Int I2
    rule I1:Int - I2:Int => I1 -Int I2
    rule I1:Int * I2:Int => I1 *Int I2
    rule I1:Int / I2:Int => I1 /Int I2
    
    rule <k> I:Id ++ => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (V => V +Int 1) ... </store>
    
    rule <k> I:Id -- => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (V => V -Int 1) ... </store>

    /* BOOLENS EXPRESSIONS RULES */

    rule I1:Int > I2:Int => I1 >Int I2
    rule I1:Int < I2:Int => I1 <Int I2
    rule I1:Int >= I2:Int => I1 >=Int I2
    rule I1:Int <= I2:Int => I1 <=Int I2
    rule I1:Int == I2:Int => I1 ==K I2
    //rule I1:Int != I2:Int => I1 =/=K I2
    rule ! true => false
    rule ! false => true
    rule true && E:BExp => E
    rule false && _ => false
    rule true || _ => true
    rule false || E:BExp => E

    /* BOOLENS EXPRESSIONS RULES */

    rule I1:String + I2:String => I1 +String I2

    /* MEMORY ALLOCATION RULES */

    rule <k> Vm:VarMod I:Id Int => Skip ... </k> //Tipo Int com auto valor
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> 0 </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> Vm:VarMod I:Id Boolean => Skip ... </k> //Tipo Boolean com auto valor
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> false </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> Vm:VarMod I:Id String => Skip ... </k> //Tipo String com auto valor
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> " " </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> Vm:VarMod (I:Id, Xs:Ids) Int => var Xs Int ... </k> //Tipo Int com auto valor [Mult]
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> 0 </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> Vm:VarMod I:Id Int = V:Int => Skip ...  </k> //Tipo Int com valor informado
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> Vm:VarMod I:Id Boolean = V:Bool => Skip ...  </k> //Tipo Boolean com valor informado
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> Vm:VarMod I:Id String = V:String => Skip ...  </k> //Tipo String com valor informado
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>

    /*rule <k> Vm:VarMod (I:Id, Xs:Ids) Vt:VarType = Vl:ValueType => Vm Xs Vt = Vl ... </k> //Tipo Int com valor informado [Mult]
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> Vl </store>
        <loc> L:Int => L +Int 1 </loc>*/

    rule <k> Vm:VarMod (I:Id, Xs:Ids) Int = V:Int => Vm Xs Int = V ... </k> //Tipo Int com valor informado [Mult]
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> Vm:VarMod (I:Id, Xs:Ids) Boolean = V:Bool => Vm Xs Boolean = V ... </k> //Tipo Boolean com valor informado [Mult]
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> Vm:VarMod (I:Id, Xs:Ids) String = V:String => Vm Xs Int = V ... </k> //Tipo String com valor informado [Mult]
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>

    /*rule <k> Vm:VarMod I:Id T:VarType => Skip ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> 0 </store>
        <loc> L:Int => L +Int 1 </loc>*/

    /* MEMORY SEARCH RULES */

    /*rule <k> I:Id = V:ValueType => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (_ => V) ... </store>*/

    rule <k> I:Id = V:AExp => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (_ => V) ... </store>

    rule <k> I:Id = V:BExp => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (_ => V) ... </store>

    rule <k> I:Id = V:SExp => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (_ => V) ... </store>
    
    rule <k> I:Id => V ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> V ... </store>

    //rule I1:Id = I2:Id => I2 ~> I1 = I2

    /*rule <k> I1:Id = I2:Id => I1 = V:Int ... </k>
        <env> ... I2 |-> L ... </env>
        <store> ... L |-> V ... </store>*/

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