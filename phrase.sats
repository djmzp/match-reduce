staload "./string.sats"

viewtypedef phrase(n: int) = list_vt(String, n)
viewtypedef Phrase = [n: nat] phrase(n)

fn phrase_new(): phrase(0)
fn phrase_copy {n: nat} (!phrase(n)): phrase(n)
fn phrase_equal(!Phrase, !Phrase): bool
fn phrase_print(!Phrase): void
fn phrase_free(Phrase): void

fn ocurrences(!Phrase, !String): int

overload = with phrase_equal
overload gcopy with phrase_copy
overload gprint with phrase_print
overload gfree with phrase_free
