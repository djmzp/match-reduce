What
====
This is the **WIP** intepreter, written in ATS, of a language that performs pattern matching and reductions of expressions (a sequence of symbols).

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
To build you'll need [ATS 2 (Postiats)](http://www.ats-lang.org/) possibly [version 0.4.0](https://sourceforge.net/projects/ats2-lang/files/ats2-lang/), and gcc / clang / tcc:

    patscc -DATS_MEMALLOC_LIBC *.dats -latslib -o mr

And then run with:

    ./mr file

If the file is not provided or does not exist, standard input will be read instead to parse rules. Parsing will stop when the program is unable to parse any more rules.

When run without errors, the interpreter is supposed to be memory clean.

TODO
====
- [ ] Wildcard patterns `_` and `...` that do not generate bindings.
- [ ] Support for comments in the code, maybe `include` and `define` macros too.
- [ ] Intrinsic functions (non-reducible expressions). Specially arithmetical and logical ones.
- [ ] Actual support for multi-dimensional rules (multiple levels).
- [ ] Add new wildcard that does not generate bindings but allows the matcher to "balance" the symbols refered to. Something like:  
        `0 0 par : =( *exp =) => ... ;`  
      that way, parenthesis would be correctly matched.
- [ ] A lot of other stuff...

