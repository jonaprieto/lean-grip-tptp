# TPTP syntax BNF reference

Target revision: **v9.3.0.1**.

The authoritative source is the [official TPTP syntax BNF][bnf]. The executable
[ANTLR grammar][antlr] is kept as an independent syntax reference. This note records
the productions implemented by the typed FOF/CNF modules; it is deliberately not a
replacement for the complete specification.

## FOF

```bnf
<fof_formula> ::= <fof_logic_formula> | <fof_sequent>
<fof_logic_formula> ::= <fof_binary_formula> | <fof_unary_formula> | <fof_unitary_formula>
<fof_binary_formula> ::= <fof_binary_nonassoc> | <fof_binary_assoc>
<fof_binary_nonassoc> ::= <fof_unit_formula> <nonassoc_connective> <fof_unit_formula>
<fof_binary_assoc> ::= <fof_or_formula> | <fof_and_formula>
<fof_or_formula> ::= <fof_unit_formula> | <fof_unit_formula> |
                     <fof_or_formula> | <fof_unit_formula>
<fof_and_formula> ::= <fof_unit_formula> & <fof_unit_formula> |
                      <fof_and_formula> & <fof_unit_formula>
<fof_unary_formula> ::= <unary_connective> <fof_unit_formula> |
                        <fof_infix_unary>
<fof_infix_unary> ::= <fof_term> != <fof_term>
<fof_unit_formula> ::= <fof_unitary_formula> | <fof_unary_formula>
<fof_unitary_formula> ::= <fof_quantified_formula> | <fof_atomic_formula> |
                          (<fof_logic_formula>)
<fof_quantified_formula> ::= <fof_quantifier> [<fof_variable_list>] :
                             <fof_unit_formula>
<fof_variable_list> ::= <variable> | <variable>, <fof_variable_list>
```

The supported typed parser intentionally excludes `<fof_sequent>` because the official
BNF marks FOFX as not yet in use.

## CNF

```bnf
<cnf_formula> ::= <cnf_disjunction> | (<cnf_formula>)
<cnf_disjunction> ::= <cnf_literal> |
                      <cnf_disjunction> | <cnf_literal>
<cnf_literal> ::= <fof_atomic_formula> |
                  ~ <fof_atomic_formula> |
                  ~ (<fof_atomic_formula>) |
                  <fof_infix_unary>
```

CNF variables are implicitly universally quantified.

## Shared lexical rules

```bnf
<atomic_word> ::= <lower_word> | <single_quoted> | <back_quoted>
<dollar_word> ::= $ <alpha_numeric>*
<dollar_dollar_word> ::= $ $ <alpha_numeric>*
<upper_word> ::= <upper_alpha> <alpha_numeric>*
<lower_word> ::= <lower_alpha> <alpha_numeric>*
<back_quoted> ::= ` <upper_word>
<distinct_object> ::= " <do_char>* "
<number> ::= <integer> | <rational> | <real>
```

Whitespace may occur between tokens. Comments may occur between tokens but are not
themselves tokens; the parser discards ordinary line and block comments.

## Semantic names used by FOF/CNF

The BNF uses `:==` for semantic productions. The typed validator therefore distinguishes
the standard defined names from system names:

```text
defined propositions: $true, $false
defined predicates:   $distinct, $less, $lesseq, $greater, $greatereq, $is_int, $is_rat
system names:         $$...
```

Unknown or unsupported dialect constructs remain available through the lossless envelope
parser and are not silently reinterpreted as typed FOF/CNF.

[bnf]: https://tptp.org/UserDocs/TPTPLanguage/SyntaxBNF.html
[antlr]: https://tptp.org/UserDocs/TPTPLanguage/TPTP.g4
