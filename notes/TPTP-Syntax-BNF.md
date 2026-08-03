# TPTP syntax BNF reference

Target revision: **v9.3.0.1** (recorded from the official header on 2026-08-03).

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
<fof_or_formula> ::= <fof_unit_formula> "|" <fof_unit_formula> |
                     <fof_or_formula> "|" <fof_unit_formula>
<fof_and_formula> ::= <fof_unit_formula> "&" <fof_unit_formula> |
                      <fof_and_formula> "&" <fof_unit_formula>
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
                      <cnf_disjunction> "|" <cnf_literal>
<cnf_literal> ::= <fof_atomic_formula> |
                  ~ <fof_atomic_formula> |
                  ~ (<fof_atomic_formula>) |
                  <fof_infix_unary>
```

CNF variables are implicitly universally quantified.

## TFF / TF0

This release implements the monomorphic TF0 profile of the TFF language. The
official TFF productions also describe TF1 and TXF syntax; those extensions are
not silently accepted by the TF0 parser.

~~~bnf
<tff_formula> ::= <tff_logic_formula>
<tff_logic_formula> ::= <tff_unitary_formula> | <tff_unary_formula> |
                        <tff_binary_formula> | <tff_defined_infix>
<tff_binary_formula> ::= <tff_binary_nonassoc> | <tff_binary_assoc>
<tff_binary_nonassoc> ::= <tff_unit_formula> <nonassoc_connective>
                          <tff_unit_formula>
<tff_binary_assoc> ::= <tff_or_formula> | <tff_and_formula>
<tff_or_formula> ::= <tff_unit_formula> "|" <tff_unit_formula> |
                     <tff_or_formula> "|" <tff_unit_formula>
<tff_and_formula> ::= <tff_unit_formula> "&" <tff_unit_formula> |
                      <tff_and_formula> "&" <tff_unit_formula>
<tff_unitary_formula> ::= <tff_quantified_formula> |
                          <tff_atomic_formula> |
                          (<tff_logic_formula>)
<tff_quantified_formula> ::= <tff_quantifier>
                             [<tff_variable_list>] :
                             <tff_unit_formula>
<tff_variable_list> ::= <tff_variable> |
                        <tff_variable>, <tff_variable_list>
<tff_variable> ::= <tff_typed_variable> | <variable>
<tff_typed_variable> ::= <variable> : <tff_atomic_type>
<tff_infix_unary> ::= <tff_unitary_term> != <tff_unitary_term>
<tff_atom_typing> ::= <untyped_atom> : <tff_top_level_type>
~~~

TF0 types used by this parser are atomic types and first-order signatures:

~~~bnf
<tff_top_level_type> ::= <tff_atomic_type> | <tff_mapping_type>
<tff_atomic_type> ::= <type_constant> | <defined_type>
<tff_mapping_type> ::= <tff_unitary_type> > <tff_atomic_type>
<tff_unitary_type> ::= <tff_atomic_type> |
                       (<tff_xprod_type>)
<tff_xprod_type> ::= <tff_unitary_type> * <tff_atomic_type> |
                     <tff_xprod_type> * <tff_atomic_type>
~~~

TPTP.TFF.TypeExpr represents atomic types, product domains, and mappings.
TPTP.TFF.validateDocument additionally enforces TF0 semantic rules: arguments
and function results are atomic and not $o, user types are declared before use,
symbols have at most one type, untyped symbols default to $i arguments, and
equality/arithmetic operands have compatible types. The official type-system
description is the reference for these rules, including $i, $o, $tType,
default typing, and arithmetic overloads.

## Shared lexical rules

```bnf
<atomic_word> ::= <lower_word> | <single_quoted> | <back_quoted>
<dollar_word> ::= $ <alpha_numeric>*
<dollar_dollar_word> ::= $ $ <alpha_numeric>*
<upper_word> ::= <upper_alpha> <alpha_numeric>*
<lower_word> ::= <lower_alpha> <alpha_numeric>*
<back_quoted> ::= ` <upper_word>
<single_quoted> ::= ' <sq_char> <sq_char>* '
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
defined terms:        $uminus, $sum, $difference, $product, $quotient, $quotient_e,
                      $quotient_t, $quotient_f, $remainder_e, $remainder_t, $remainder_f,
                      $floor, $ceiling, $truncate, $round, $to_int, $to_rat, $to_real
system names:         $$...
```

Unknown or unsupported dialect constructs remain available through the lossless envelope
parser and are not silently reinterpreted as typed FOF/CNF.

[bnf]: https://tptp.org/UserDocs/TPTPLanguage/SyntaxBNF.html
[antlr]: https://tptp.org/UserDocs/TPTPLanguage/TPTP.g4
