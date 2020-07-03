#define ATS_DYNLOADFLAG 0

staload "./dictionary.sats"
staload "./phrase.sats"
staload "./string.sats"

implement dictionary_new() = list_vt_nil()

implement dictionary_print(dict) =
	case+ dict of
	| list_vt_nil() => ()
	| list_vt_cons(t, xs) => (
		print!(t.0, " = ");
		phrase_print(t.1);
		println!();
		dictionary_print(xs)
	)

implement dictionary_free(dict) =
	case+ dict of
	| ~list_vt_nil() => ()
	| ~list_vt_cons(t, xs) => (
		string_free(t.0);
		phrase_free(t.1);
		dictionary_free(xs)
	)
