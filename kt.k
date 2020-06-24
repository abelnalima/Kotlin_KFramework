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
                | WhileStmt
                | DoWhileStmt
                | AExp
                | AExpMod
                | BExp
                //| SExp
                | ForStmt
                | ForEachStmt
                | FuncDec
                | FuncCall

    syntax Params ::= List{Id, ","}
    syntax FuncDec ::= "function" Id "(" Params ")"  Block
                    | "fun" Id "(" Params ")" ":" "Int" Block
    syntax FuncCall ::= Id "(" ListValues ")"
    syntax Local ::= "local" "(" Id "," Stmt ")"
              //  | "local" "(" VarMod Id Int "," Stmt ")"

    syntax VarType ::= "Int" 
                    | "Boolean" 
                    | "String"

    syntax VarMod ::= "var" | "val"

    syntax VarDeclaration ::= VarMod Ids "Int"
                        | VarMod Ids "Boolean"
                        | VarMod Ids "String"
                        //| VarMod Ids
                        //| VarMod Ids VarType

    //syntax ValueType ::= Int | Bool | String //| Id

    syntax Ids ::= List{Id, ","}
    syntax ListValues ::= List{Int, ","}
    syntax ArrayList ::= "[" ListValues "]"

    syntax Assigner ::= VarDeclaration "=" AExp [strict(2)]
                    | VarDeclaration "=" BExp [strict(2)]
                    //| VarDeclaration "=" SExp [strict(2)]
                    | VarDeclaration "=" IdExp

    syntax IdAssigner ::= Id "=" AExp [strict(2)]
                    | Id "=" BExp [strict(2)]
                    //| Id "=" SExp [strict(2)]
                    | Id "=" IdExp
                    | "var" Id "=" AExp [strict(2)]
                    | "var" Id "=" IdExp
                    //| Id "=" ValueType

    syntax AExp ::= Int
                | String
                | Id
                > left: AExp "*" AExp [seqstrict, left]
                > left: AExp "/" AExp [seqstrict, left]
                //| AExp "+" AExp [seqstrict]
                | AExp "-" AExp [seqstrict, left]
                | Int "+" AExp [seqstrict, left]
                | String "+" AExp [seqstrict, left]
                //| Id
                | "(" AExp ")" [bracket]

    syntax AExpMod ::= Id "++"
                | Id "--"
                //| Int"++"

    syntax BExp ::= Bool
                | AExp ">" AExp [strict]
                | AExp "<" AExp [strict]
                | AExp ">=" AExp [strict]
                | AExp "<=" AExp [strict]
                | AExp "==" AExp [strict]
                //| Id
                > "!" BExp [seqstrict, left]
                > left: BExp "&&" BExp [strict]
                | BExp "||" BExp [strict, left]
                | "(" BExp ")" [bracket]

    /*syntax SExp ::= String
                //| Id
                | String "+" SExp [seqstrict, left]*/

    syntax IdExp ::= Id "+" Id

    syntax IfStmt ::= "if" "(" BExp ")" Block [strict(1)]
                | "if" "(" BExp ")" Block ElseIfStmt [strict(1)]

    syntax ElseIfStmt ::= "else if" "(" BExp ")" Block
                    | "else if" "(" BExp ")" Block ElseIfStmt
                    | "else" Block

    syntax WhileStmt ::= "while" "(" BExp ")" Block

    syntax DoWhileStmt ::= "do" Block "while" "(" BExp ")"

    syntax ForStmt ::= "for" "(" IdAssigner ";" BExp ";" AExpMod ")" Block
                    //| "for" "(" IdAssigner "in" Int ".." Int ")" Block

    syntax ForEachStmt ::= "foreach" "(" Id "in" ArrayList ")" Block
    
    //syntax RangeStmt ::= "in" Int ".." Int

    /* REWRITE RULES */

    rule Skip => .

    rule fun main() {B:Block} => B [structural]

    rule S1:Stmt S2:Stmt => S1 ~> S2 [structural]
    rule local ( I:Id, S1:Stmt S2:Stmt ) => local ( I , S1) ~> local ( I , S2) [structural]
    //rule local ( Vm:VarMod I:Id Int, S1:Stmt S2:Stmt ) => local (Vm I Int, S1) ~> local ( Vm I Int, S2) [structural]

    rule V:VarMod .Ids Int => Skip
    rule V:VarMod .Ids Boolean => Skip
    rule V:VarMod .Ids String => Skip
    rule V:VarMod .Ids Int = _:Int => Skip
    rule V:VarMod .Ids Boolean = _:Bool => Skip
    rule V:VarMod .Ids String = _:String => Skip
    //rule .Ids Stmt => Skip
    //rule var .Ids = _:Int => Skip
    //rule I:Int => Skip

    rule if (true) { S:Stmt } => S
    rule if (false) { _ } => Skip
    rule if (true) { S:Stmt } Sif:ElseIfStmt => S
    rule if (false) { _ } S:ElseIfStmt => S
    rule else if (E:BExp) { S1:Stmt } S2:ElseIfStmt => if (E) { S1 } S2
    rule else if (E:BExp) { S:Stmt } => if (E) { S }
    rule else { S:Stmt } => S
    rule if (true) { S:Stmt } else _ => S
    rule if (false) { _ } else { S:Stmt } => S

    rule while (E:BExp) {S:Stmt} => if (E) { S while (E) { S } } [structural]
    rule do { S:Stmt } while (E:BExp) => S ~> if (E) { do { S } while (E) } [structural]

    rule for (I:Id = E1:AExp ; E2:BExp ; E3:AExpMod) { S:Stmt }
        => I = E1 ~> while (E2) { S E3} [structural]
    /*rule for (I1:Id = E1:AExp in I2:Int .. I3:Int) { S:Stmt }
        => I1 = E1 ~> if (I2 < I3) { S I2++ I1 = I2}*/

    //rule in I1:Int .. I2:Int => while (I1 < I2) {  }

    rule foreach ( I:Id in [ .ListValues ] ) B:Block => Skip
 
    /* ARITHMETHIC EXPRESSIONS RULES */

    rule I1:Int + I2:Int => I1 +Int I2
    rule I1:Int - I2:Int => I1 -Int I2
    rule I1:Int * I2:Int => I1 *Int I2
    rule I1:Int / I2:Int => I1 /Int I2 when I2 =/=Int 0
    
    rule <k> I:Id ++ => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (V => V +Int 1) ... </store>
    
    rule <k> I:Id -- => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (V => V -Int 1) ... </store>

    //rule I:Int++ => I +Int 1

    /*rule <k> I:Int ++ => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (V => V +Int 1) ... </store>*/

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

    /* STRINGS EXPRESSIONS RULES */

    rule I1:String + I2:String => I1 +String I2

    /* ID's EXPRESSIONS RULES */

    rule <k> I1:Id = I2:Id + I3:Id => I1 = V + I3 ... </k>
        <env> ... I2 |-> L ... </env>
        <store> ... L |-> V:Int ... </store>

    rule <k> I1:Id = I2:Int + I3:Id => I1 = I2 + V ... </k>
        <env> ... I3 |-> L ... </env>
        <store> ... L |-> V:Int ... </store>

    rule <k> I1:Id = I2:Id - I3:Id => I1 = V - I3 ... </k>
        <env> ... I2 |-> L ... </env>
        <store> ... L |-> V:Int ... </store>

    rule <k> I1:Id = I2:Int - I3:Id => I1 = I2 - V ... </k>
        <env> ... I3 |-> L ... </env>
        <store> ... L |-> V:Int ... </store>

    rule <k> I1:Id = I2:Id * I3:Id => I1 = V * I3 ... </k>
        <env> ... I2 |-> L ... </env>
        <store> ... L |-> V:Int ... </store>

    rule <k> I1:Id = I2:Int * I3:Id => I1 = I2 * V ... </k>
        <env> ... I3 |-> L ... </env>
        <store> ... L |-> V:Int ... </store>

    rule <k> I1:Id = I2:Id / I3:Id => I1 = V / I3 ... </k>
        <env> ... I2 |-> L ... </env>
        <store> ... L |-> V:Int ... </store>

    rule <k> I1:Id = I2:Int / I3:Id => I1 = I2 / V ... </k>
        <env> ... I3 |-> L ... </env>
        <store> ... L |-> V:Int ... </store>

    /*rule <k> I1:Id = I2:Id + I3:Id => I1 = V + I3 ... </k>
        <env> ... I2 |-> L ... </env>
        <store> ... L |-> V:String ... </store>

    rule <k> I1:Id = I2:String + I3:Id => I1 = I2 + V ... </k>
        <env> ... I3 |-> L ... </env>
        <store> ... L |-> V:String ... </store>*/

    rule <k> Vm:VarMod I1:Id Int = I2:Id + I3:Id => Vm I1 Int = V + I3 ... </k>
        <env> ... I2 |-> L ... </env>
        <store> ... L |-> V:Int ... </store>

    rule <k> Vm:VarMod I1:Id Int = I2:Int + I3:Id => Vm I1 Int = I2 + V ... </k>
        <env> ... I3 |-> L ... </env>
        <store> ... L |-> V:Int ... </store>

    rule <k> Vm:VarMod I1:Id Int = I2:Id - I3:Id => Vm I1 Int = V - I3 ... </k>
        <env> ... I2 |-> L ... </env>
        <store> ... L |-> V:Int ... </store>

    rule <k> Vm:VarMod I1:Id Int = I2:Int - I3:Id => Vm I1 Int = I2 - V ... </k>
        <env> ... I3 |-> L ... </env>
        <store> ... L |-> V:Int ... </store>

    rule <k> Vm:VarMod I1:Id Int = I2:Id * I3:Id => Vm I1 Int = V * I3 ... </k>
        <env> ... I2 |-> L ... </env>
        <store> ... L |-> V:Int ... </store>

    rule <k> Vm:VarMod I1:Id Int = I2:Int * I3:Id => Vm I1 Int = I2 * V ... </k>
        <env> ... I3 |-> L ... </env>
        <store> ... L |-> V:Int ... </store>

    rule <k> Vm:VarMod I1:Id Int = I2:Id / I3:Id => Vm I1 Int = V / I3 ... </k>
        <env> ... I2 |-> L ... </env>
        <store> ... L |-> V:Int ... </store>

    rule <k> Vm:VarMod I1:Id Int = I2:Int + I3:Id => Vm I1 Int = I2 + V ... </k>
        <env> ... I3 |-> L ... </env>
        <store> ... L |-> V:Int ... </store>

    rule <k> Vm:VarMod I1:Id String = I2:Id + I3:Id => Vm I1 String = V + I3 ... </k>
        <env> ... I2 |-> L ... </env>
        <store> ... L |-> V:String ... </store>

    rule <k> Vm:VarMod I1:Id String = I2:Int + I3:Id => Vm I1 String = I2 + V ... </k>
        <env> ... I3 |-> L ... </env>
        <store> ... L |-> V:String ... </store>

    rule <k> var I1:Id = I2:Id + I3:Id => var I1 = V + I3 ... </k>
        <env> ... I2 |-> L ... </env>
        <store> ... L |-> V:Int ... </store>

    rule <k> var I1:Id = I2:Int + I3:Id => var I1 = I2 + V ... </k>
        <env> ... I3 |-> L ... </env>
        <store> ... L |-> V:Int ... </store>
    
    /* LOCAL EXPRESSION RULES */

    //local ( sum , var x = 10 + 20 )
    rule <k> local(FuncId:Id, var I:Id = V1:Int + V2:Int) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> (V1 +Int V2) </store>
        <loc> L => L +Int 1 </loc>

    rule <k> local(FuncId:Id, var I1:Id = I2:Id + I3:Id) => local(FuncId, var I1 = V + I3) ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I2 |-> L ... </localEnv>
            ...
        </thread>
        <store> ... L |-> V:Int ... </store>

    rule <k> local(FuncId:Id, var I1:Id = I2:Int + I3:Id) => local(FuncId, var I1 = I2 + V) ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I3 |-> L ... </localEnv>
            ...
        </thread>
        <store> ... L |-> V:Int ... </store>

    //local ( sum , var x = a )
    rule <k> local(FuncId:Id, var I1:Id = I2:Id) => local(FuncId, var I1 = V) ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I2 |-> L ... </localEnv>
            ...
        </thread>
        <store> ... L |-> V:Int ... </store>

    /* MEMORY ALLOCATION RULES */

    /*rule <k> Vm:VarMod I:Id Int => Skip ... </k> //Tipo Int com auto valor
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
        <loc> L:Int => L +Int 1 </loc>*/

    rule <k> Vm:VarMod (I:Id, Xs:Ids) Int => Vm Xs Int ... </k> //Tipo Int com auto valor [Mult]
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> 0 </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> Vm:VarMod (I:Id, Xs:Ids) Boolean => Vm Xs Boolean ... </k> //Tipo Boolean com auto valor [Mult]
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> false </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> Vm:VarMod (I:Id, Xs:Ids) String => Vm Xs String ... </k> //Tipo String com auto valor [Mult]
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> " " </store>
        <loc> L:Int => L +Int 1 </loc>

    /*rule <k> Vm:VarMod I:Id Int = V:Int => Skip ...  </k> //Tipo Int com valor informado
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
        <loc> L:Int => L +Int 1 </loc>*/

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

    rule <k> Vm:VarMod (I:Id, Xs:Ids) String = V:String => Vm Xs String = V ... </k> //Tipo String com valor informado [Mult]
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>

    /*rule <k> Vm:VarMod I:Id T:VarType => Skip ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> 0 </store>
        <loc> L:Int => L +Int 1 </loc>*/

    rule <k> var I:Id = V:Int => Skip ... </k> //Tipo Int com valor informado
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> foreach ( I:Id in [ (V:Int, Vs:ListValues) ] ) { S:Stmt }
            => S ~> foreach ( I in [Vs:ListValues] ) { S } ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>
        when notBool (I in keys(MEnv))

    rule <k> foreach ( I:Id in [ (V:Int, Vs:ListValues) ] ) { S:Stmt }
            => S ~> foreach ( I in [Vs:ListValues] ) { S } ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> ( _ => V ) </store>

    /* MEMORY SEARCH RULES */

    /*rule <k> I:Id = V:ValueType => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (_ => V) ... </store>*/

    rule <k> I:Id = V:AExp => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (_ => V) ... </store>

    /*rule <k> var I:Id = V:AExp => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (_ => V) ... </store>*/

    rule <k> I:Id = V:BExp => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (_ => V) ... </store>

    /*rule <k> I:Id = V:SExp => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (_ => V) ... </store>*/
    
    rule <k> I:Id => V ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> V ... </store>

    rule <k> var I1:Id = I2:Id => var I1 = V ... </k>
        <env> ... I2 |-> L ... </env>
        <store> ... L |-> V:Int ... </store>

    /* FUNCTION RULES */

    /*rule <k> function I:Id (P:Params) { S:Stmt } => Skip ... </k>
        ( .Bag =>
            <thread>
                <id> I </id>
                <scope> S </scope>
                <params> P </params>
                <temp> P </temp>
                <localEnv> .Map </localEnv>
            </thread>
        )*/

    rule <k> fun I:Id (P:Params) : Int { S:Stmt } => Skip ... </k>
        ( .Bag =>
            <thread>
                <id> I </id>
                <scope> S </scope>
                <params> P </params>
                <temp> P </temp>
                <localEnv> .Map </localEnv>
            </thread>
        )

    rule <k> I:Id (.ListValues) => local(I, S) ... </k>
        <thread>
            ...
            <id> I </id>
            <scope> S:Stmt </scope>
            <params> P </params>
            <temp> (.Params => P) </temp>
            ...
        </thread>

    /*rule <k> I:Id (.ListValues) => local(I, S) ... </k>
        <thread>
            ...
            <id> I </id>
            <scope> S:Stmt </scope>
            <params> P </params>
            <temp> (.Params => P) </temp>
            ...
        </thread>*/

    rule <k> I:Id ((V:Int, Vs:ListValues)) => I:Id (Vs) ... </k>
        <thread>
            ...
            <id> I </id>
            <temp> ((P:Id, Ps:Params) => Ps) </temp>
            <localEnv> Rho:Map => Rho P |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> V </store>
        <loc> L => L +Int 1 </loc>

    rule <k> local(FuncId:Id, var I:Id = V:Int) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> Rho:Map => Rho I |-> L </localEnv>
            ...
        </thread>
        <store> SMap:Map => SMap L |-> V </store>
        <loc> L => L +Int 1 </loc>

    rule <k> local(FuncId:Id, I:Id = V:Int) => Skip ... </k>
        <thread>
            ...
            <id> FuncId </id>
            <localEnv> ... I |-> L ... </localEnv>
            ...
        </thread>
        <store> ... L |-> (_ => V) </store>

    /* CONFIGURATIONS */

    configuration <T> 
        <k color = "green"> $PGM:Fun </k>
        <functions color="orange">
            <thread multiplicity="*" color="blue" type="Map">
                <id> .K </id>
                <scope> .K </scope>
                <params> .K </params>
                <temp> .K </temp>
                <localEnv> .Map </localEnv>
            </thread>
        </functions>
        <env> .Map </env>
        <store color = "yellow"> .Map </store>
        <loc> 1 </loc>
     
    </T>

endmodule

module KT

    import DOMAINS
    import KT-SYNTAX
    syntax KResult ::= Int | Bool | String
    syntax KVariable ::= Id

endmodule