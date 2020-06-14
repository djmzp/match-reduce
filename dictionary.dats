#define ATS_DYNLOADFLAG 0

staload "dictionary.sats"
staload "expression.sats"

implement dictionary_new() = list_vt_nil()

implement dictionary_print(dict) =
	case+ dict of
	| list_vt_nil() => ()
	| list_vt_cons(x, xs) => (
		print!(x.0, " = ");
		expression_print(x.1);
		println!();
		dictionary_print(xs)
	)

implement dictionary_free(dict) =
	case+ dict of
	| ~list_vt_nil() => ()
	| ~list_vt_cons((s, def), xs) => (
		strptr_free(s);
		expression_free(def);
		dictionary_free(xs)
	)
