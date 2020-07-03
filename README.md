An experiment. I just wanted to do an ATS project and thought this was a good enough concept so I started one.

This is the **WIP** intepreter, written in ATS, of a language that performs a pattern match on some expression (a sequence of symbols) and reduces 
that expression. Both the pattern and the resulting expression (skeleton) are given via rules to the interpreter following the format:

    <level> <precedence> <name> : <pattern> => <skeleton> ;

The current implementation is very similar to the one found in [Lecture 4A of SICP](https://www.youtube.com/watch?v=amf5lTZ0UTc) and is memory clean if 
no errors are encountered.

Examples are located in the `test` directory. Some of them may work some may not :)

To build you'll probably need ATS version 0.4.0 and gcc / clang / tcc:

    patscc -DATS_MEMALLOC_LIBC main.dats skeleton.dats pattern.dats phrase.dats dictionary.dats string.dats -latslib -o mr

And then run with:
   
    ./mr test-file
    
If the file is not provided, the interpreter will read from standard input.

**This README will be updated in the future**
