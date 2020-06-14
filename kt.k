module KT-SYNTAX
    import DOMAINS

    syntax Fun ::= "fun" "main" "(" ")" "{" "}"

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