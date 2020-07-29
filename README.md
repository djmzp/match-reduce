What
====
This is the **WIP** intepreter, written in ATS, of a language that performs pattern matching and reductions of expressions (a sequence of symbols).
Basically... a term rewriting system.

The current implementation is very similar to the one found in [Lecture 4A of SICP](https://www.youtube.com/watch?v=amf5lTZ0UTc) only that the original
reduces lisp expressions and this one reduces sequence of symbols, which implies that this implementation is more prone to ambiguity.
It is also **very** inefficient as it relies on linked lists instead of arrays and the way of processing data could be improved as it also includes lots
of list reversing and some non tail recursive functions.

This implementation is also not homoiconic and does not have support for _first class citizen_ rules.

Rule format
===========
Both the pattern and the skeleton of the expression to be instantiated are given via rules to the interpreter following the format:

    <level> <precedence> <name> : <pattern> => <skeleton> ;

- Level and precedence are integers (constrained to the size of a normal `int` type, no arbitrary precision arithmetic is used).
- Name is a normal symbol.
- Pattern is a sequence of symbols and wildcards:
    - `x` matches `x`.
    - `?x` matches any symbol and creates a binding.
    - `*x` matches a sequence of zero or more symbols in a _non-greedy_ way and creates binding. Still pondering as to how to interpret it correctly.
- Skeleton is a sequence of symbols and wildcards:
    - `x` reduces to `x`.
    - `:x` reduces to the symbol or sequence of symbols that were bound to the pattern variable `x`.

Keep in mind that a symbol is defined to be as a sequence of one or more characters, separated by a space, `'\t'`, `'\n'`, `'\v'`, `'\f'` or `'\r'`.
The symbol `=>` may **not** be used inside of a pattern as it is used as a delimiter. Same goes for `;` inside a skeleton. Also symbols of the form `?x`/`*x` are
allowed inside of skeletons and will be reduced to exacty `?x`/`*x`.

Examples are located in the `test` directory. Some of them may work some may not :)

Build & run
===========
To build you'll need [ATS 2 (Postiats)](http://www.ats-lang.org/) possibly [version 0.4.0](https://sourceforge.net/projects/ats2-lang/files/ats2-lang/), [gmp](https://gmplib.org), and gcc / clang / tcc:

    patscc -I ${PATSHOME}/contrib/atscntrb -D ATS_MEMALLOC_LIBC *.dats -l atslib -l gmp -o main

(Make sure that the `PATSHOME` variable is defined). Then run with:

    ./mr file

If the file is not provided or does not exist, standard input will be read instead to parse rules. Parsing will stop when the program is unable to parse any more rules.

When run without errors, the interpreter is supposed to be memory clean.

GMP errors
----------
 If you run into errors with the C compiler complaining about `atscntrb_gmp_mpz_set_mpz` not being defined, edit the file
`$PATSHOME/contrib/atscntrb/atscntrb-hx-libgmp/CATS/gmp.cats`, adding:

```C
#define atscntrb_gmp_mpz_set_str mpz_set_str
```
Somewhere in the file.

TODO
====
- [x] Wildcard patterns `_` and `...` that do not generate bindings.
- [ ] Support for comments in the code, maybe `include` and `define` macros too.
    - [x] Multi-line comments are now supported but `/*` and `*/` are still treated like individual symbols so they also have to be limited by whitespaces.
- [x] Intrinsic functions (non-reducible expressions). Specially arithmetical and logical ones.
- [ ] Actual support for multi-dimensional rules (multiple levels).
- [ ] Add new wildcard that does not generate bindings but allows the matcher to "balance" the symbols refered to. Something like:
        `0 0 par : =( *exp =) => ... ;`
      that way, parenthesis would be correctly matched.
- [ ] ~~Add new skeleton wildcard that reduces an expression right after instantiating it.~~ Done by default.
- [ ] Add suport of literals: numbers, strings, characters...
- [ ] ~~Add another kind of rule that implicitly inserts `...` at both ends of the pattern.~~ Bad idea: the head and the tail of the phrase will be discarded with the current matcher.
- [ ] A lot of other stuff...

LICENSE
=======
Unless *explicitly* stated inside of an individual file, the code is under the MIT/X11 license.
Check [LICENSE](LICENSE) for more information.
