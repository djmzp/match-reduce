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

    <level> <precedence> <name> : <pattern> <arrow> <skeleton> ;

- Level and precedence are integers (constrained to the size of a normal `int` type, no arbitrary precision arithmetic is used).
- Name is a normal symbol.
- Pattern is a sequence of symbols and wildcards:
    - `x` matches `x`.
    - `?x` matches any symbol and creates a binding.
    - `*x` matches a sequence of zero or more symbols in a _non-greedy_ way and creates binding. Still pondering as to how to interpret it correctly.
- Arrow may be one of:
    - `=>` does not reduce immediately after matching and instantiating the expression.
    - `=>>` reduces immediately after matching and instantiating the expression (atomically).
- Skeleton is a sequence of symbols and wildcards:
    - `x` reduces to `x`.
    - `:x` reduces to the symbol or sequence of symbols that were bound to the pattern variable `x`.

Keep in mind that a symbol is defined to be as a sequence of one or more characters, separated by a space, `'\t'`, `'\n'`, `'\v'`, `'\f'` or `'\r'`.
The symbols `=>` or `=>>` may **not** be used inside of a pattern as they are used as a delimiters. Same goes for `;` inside a skeleton. Also symbols
of the form `?x`/`*x` are allowed inside of skeletons and will be reduced to exacty `?x`/`*x`.

Examples are located in the `test` directory. Some of them may work some may not :)

Build & run
===========
To build you'll need [ATS 2 (Postiats)](http://www.ats-lang.org/) possibly [version 0.4.0](https://sourceforge.net/projects/ats2-lang/files/ats2-lang/), [gmp](https://gmplib.org), and gcc / clang / tcc:

    patscc -I ${PATSHOME}/contrib/atscntrb -D ATS_MEMALLOC_LIBC *.dats -l atslib -l gmp -o mr

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

Warning (memory usage)
======================
This program is **really** heavy on memory usage. For instance, the brainf*ck interpreter [test/17](test/17), when interpreting the `hello-world` program allocates about 500 MB:

    ==5195== Memcheck, a memory error detector
    ==5195== Copyright (C) 2002-2017, and GNU GPL'd, by Julian Seward et al.
    ==5195== Using Valgrind-3.16.1 and LibVEX; rerun with -h for copyright info
    ==5195== Command: ./main test/17
    ==5195==
    Reductions:
    Hello World!

    Final expression
    0: [[ 0 0 72 100 87 33 ^ 10 0 0 0 0 0 0 0 0 ]]
    1: main
    ==5195==
    ==5195== HEAP SUMMARY:
    ==5195==     in use at exit: 26 bytes in 13 blocks
    ==5195==   total heap usage: 49,927,837 allocs, 49,927,824 frees, 490,226,008 bytes allocated
    ==5195==
    ==5195== LEAK SUMMARY:
    ==5195==    definitely lost: 26 bytes in 13 blocks
    ==5195==    indirectly lost: 0 bytes in 0 blocks
    ==5195==      possibly lost: 0 bytes in 0 blocks
    ==5195==    still reachable: 0 bytes in 0 blocks
    ==5195==         suppressed: 0 bytes in 0 blocks
    ==5195== Rerun with --leak-check=full to see details of leaked memory
    ==5195==
    ==5195== For lists of detected and suppressed errors, rerun with: -s
    ==5195== ERROR SUMMARY: 0 errors from 0 contexts (suppressed: 0 from 0)

_huh? Memory... leaking? No way!_

So why?
-------
There are multiple reasons that explain the high memory usage:
1. The implementation is bad:  
Don't get me wrong, ATS programs won't (normally... _ahem_) leak memory. Linear types are definitely a helping factor when it comes into lowering memory usage.
The problem is that this implementation relies a lot on linear linked lists (`list_vt`) and the `match` function (and others too) are *very* recursive, so a lot of
the data that is allocated doesn't get free'd immediatelly and more importantly, memory just gets wasted: there's a lot of copying and very little reusing.  
A good solution for this would be to use arrays and try to reuse as much memory as possible. Also don't use recursion so much.
2. The programs that are being interpreted may be very recursive, such as the [brainf*ck](test/17) interpreter, so the interpreter interpreting the interpreter suffers
from that too.

If this had been done in, say C, it would have likely been more memory and CPU friendly. The implementation would have been a lot more cleaner and overall better to look
at.  
Regardless this project was made for the sake of using ATS and nothing more.

TODO
====
- [x] Wildcard patterns `_` and `...` that do not generate bindings.
- [ ] Support for comments in the code, maybe `include` and `define` macros too.
    - [x] Multi-line comments are now supported but `/*` and `*/` are still treated like individual symbols so they also have to be delimited by whitespaces.
- [x] Intrinsic functions (non-reducible expressions). Specially arithmetical and logical ones.
- [ ] Actual support for multi-dimensional rules (multiple levels).
- [x] Add new wildcard that does not generate bindings but allows the matcher to "balance" the symbols refered to. Something like:
        `0 0 par : =( *exp =) => ... ;`
      that way, parenthesis would be correctly matched.
- [ ] ~~Add new skeleton wildcard that reduces an expression right after instantiating it.~~ Done by default.
- [ ] Add suport of literals: numbers, strings, characters... (somewhat done).
- [ ] ~~Add another kind of rule that implicitly inserts `...` at both ends of the pattern.~~ Bad idea: the head and the tail of the phrase will be discarded with the current matcher.
- [ ] A lot of other stuff...

LICENSE
=======
Unless *explicitly* stated inside of an individual file, the code is under the MIT/X11 license.
Check [LICENSE](LICENSE) for more information.
