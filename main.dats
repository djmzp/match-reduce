#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0

/*
	100 r_sum: ?x + ?y => $sum :x :y ;
*/

overload close with fileref_close

dataviewtype Pat =
	| pat_symbol of Strptr1	// w+
	| pat_atom of Strptr1	// ?w+
	| pat_mult of Strptr1	// *w+

dataviewtype Ske =
	| ske_symbol of Strptr1	// w+
	| ske_hole of Strptr1	// :w+

viewtypedef expression(n: int) = list_vt(Strptr1, n)
viewtypedef Expression = [n: nat] expression(n)

viewtypedef pattern(n: int) = list_vt(Pat, n)
viewtypedef Pattern = [n: nat] pattern(n)

viewtypedef skeleton(n: int) = list_vt(Ske, n)
viewtypedef Skeleton = [n: nat] skeleton(n)

viewtypedef Rule = @{
	precedence = int,
	name = string,
	pattern = Pattern,
	skeleton = Skeleton
}

fn pattern_free(pat: Pattern): void =
	let
		implement list_vt_freelin$clear<Pat>(e) =
			case+ e of
			| ~pat_symbol(s) => strptr_free(s)
			| ~pat_atom(s) => strptr_free(s)
			| ~pat_mult(s) => strptr_free(s)
	in
		list_vt_freelin<Pat>(pat)
	end

fn pat_print(pat: !Pat): void =
	case+ pat of
	| pat_symbol(s) => print(s)
	| pat_atom(s) => (print("?"); print(s))
	| pat_mult(s) => (print("*"); print(s))

fn ske_print(ske: !Ske): void =
	case+ ske of
	| ske_symbol(s) => print(s)
	| ske_hole(s) => (print(":"); print(s))

overload print with pat_print
overload print with ske_print

// TODO why doesnt ATS like my print implementations?????
fun pattern_print(pat: !Pattern): void =
	case+ pat of
	| list_vt_cons(p, ps) => (
		print(p);
		print(" ");
		pattern_print(ps)
	)
	| list_vt_nil() => ()

overload gprint with pattern_print

fun skeleton_print(ske: !Skeleton): void =
	case+ ske of
	| list_vt_cons(s, ss) => (
		print(s);
		print(" ");
		skeleton_print(ss)
	)
	| list_vt_nil() => ()

overload gprint with skeleton_print

// overload fprint with pattern_list_print

fn expression_free(exp: Expression): void =
	let
		implement list_vt_freelin$clear<Strptr1>(s) = strptr_free(s)
	in
		list_vt_freelin<Strptr1>(exp)
	end

// overload free with expression_free <- doesnt even work

fn expression_copy(exp: !Expression): Expression =
	let
		implement list_vt_copylin$copy<Strptr1>(s) = strptr1_copy(s)
	in
		list_vt_copylin<Strptr1>(exp)
	end

fun expression_print(exp: !Expression): void =
	case+ exp of
	| list_vt_cons(s, es) => (
		print_strptr(s);
		print(" ");
		expression_print(es)
	)
	| list_vt_nil() => ()

overload gprint with expression_print

fun expression_equal(ex1: !Expression, ex2: !Expression): bool =
	case+ (ex1, ex2) of
	| (list_vt_nil(), list_vt_nil()) => true
	| (list_vt_cons(e1, es1), list_vt_cons(e2, es2)) =>
		if compare_strptr_strptr(e1, e2) = 0 then
			true
		else
			expression_equal(es1, es2)
	| (_, _) => false

overload = with expression_equal

#define :: list_vt_cons

viewtypedef dictionary(n: int) = list_vt(@(Strptr1, Expression), n)
viewtypedef Dictionary = [n: nat] dictionary(n)

fn expression_new(): Expression = list_vt_nil()

fn dictionary_new(): Dictionary = list_vt_nil()

fun dictionary_free(dict: Dictionary): void =
	case+ dict of
	| ~list_vt_nil() => ()
	| ~(s, def)::xs => (
		strptr_free(s);
		expression_free(def);
		dictionary_free(xs)
	)

fun dictionary_print(dict: !Dictionary): void =
	case+ dict of
	| list_vt_nil() => ()
	| x::xs => (
		print!(x.0, " = ");
		expression_print(x.1);
		println!();
		dictionary_print(xs)
	)

overload gprint with dictionary_print

fun lookup(symbol: !Strptr1, dict: !Dictionary): Option_vt(Expression) =
	case+ dict of
	| list_vt_cons(x, ds) when compare_strptr_strptr(x.0, symbol) = 0 =>
		Some_vt(expression_copy(x.1))
	| list_vt_cons(_, ds) => lookup(symbol, ds)
	| list_vt_nil() => None_vt()


fn skeleton_free(ske: Skeleton): void =
	let
		implement list_vt_freelin$clear<Ske>(s) =
			case+ s of
			| ~ske_symbol(s) => strptr_free(s)
			| ~ske_hole(s) => strptr_free(s)
	in
		list_vt_freelin<Ske>(ske)
	end

fn match(pat: !Pattern, exp: !Expression): Option_vt(Dictionary) =
	let
		val dict = dictionary_new();

		fun loop {n: nat} (pat: !Pattern, exp: !Expression, dict: dictionary(n), temp: Expression): Option_vt(Dictionary) =
			case+ (pat, exp) of
			| (pat_symbol(s1)::ps, s2::es) when compare(s2, s1) = 0 => loop(ps, es, dict, temp) where {
				// XXX ????? why am I extending the dictionary here anyways
				// val dict' = list_vt_extend(dict, (s1, s2 :: list_vt_nil))
			}
			| (pat_symbol(s1)::ps, s2::es) => (
				dictionary_free(dict);
				expression_free(temp);
				None_vt()
			)
			| (pat_atom(s1)::ps, s2::es) => loop(ps, es, dict', temp) where {
				// val dict' = list_vt_extend(dict, (strptr1_copy(s1), strptr1_copy(s2) :: list_vt_nil))
				val dict' = list_vt_cons((strptr1_copy(s1), strptr1_copy(s2) :: list_vt_nil), dict)
			}
			// PATTERN: some thing *what ever => ...  |||| and the expression is empty, dont match
			| (pat_mult(s1)::_, list_vt_nil()) => (
				expression_free(temp);
				Some_vt(dict)
			)
			// PATTERN: some thing *end => ...
			| (pat_mult(s1)::list_vt_nil(), _) => Some_vt(dict') where {
				val () = expression_free(temp)
				// val dict' = list_vt_extend(dict, (strptr1_copy(s1), expression_copy(exp)))
				val dict' = list_vt_cons((strptr1_copy(s1), expression_copy(exp)), dict)
			}
			// PATTERN: some thing *alot end => ...
			| (pat_mult(s1)::pat_symbol(lookahead)::ps, s2::es) when compare(s2, lookahead) = 0 =>
			let
				val temp' = expression_copy(temp)
				val () = expression_free(temp)
				val temp = $list_vt{Strptr1}()
				// val dict' = list_vt_extend(dict, (strptr1_copy(s1), temp'))
				val dict' = list_vt_cons((strptr1_copy(s1), temp'), dict)
			in
				loop(ps, es, dict', temp)
			end

			| (pat_mult(s1)::pat_symbol(lookahead)::ps, s2::es) =>
			let
				// XXX this used to be extend
				// val tmp = list_vt_append(temp, s2::list_vt_nil())
				// val tmp = list_vt_extend(temp, strptr1_copy(s2))
				val tmp = list_vt_cons(strptr1_copy(s2), temp)
			in
				loop(pat, es, dict, tmp)
			end
			// XXX maybe not?
			| (list_vt_nil(), _) => (
				expression_free(temp);
				Some_vt(dict)
			)

			| (_, _) => (
				// Lets try to be positive
				// dictionary_free(dict);
				expression_free(temp);
				Some_vt(dict)
			)

	in
		loop(pat, exp, dict, $list_vt{Strptr1}())
	end


fn instantiate(ske: !Skeleton, dict: !Dictionary): Option_vt(Expression) =
	let
		val exp: Expression = expression_new()
		fun loop(ske: !Skeleton, dict: !Dictionary, exp: Expression): Option_vt(Expression) =
			case+ ske of
			| ske_symbol(s)::ss => loop(ss, dict, exp') where {
				// XXX this used to be extend
				val exp' = list_vt_append(strptr1_copy(s)::list_vt_nil, exp)
			}
			| ske_hole(s)::ss => (
				case+ lookup(s, dict) of
				// TODO way too many (two, to be exact) reverses
				| ~Some_vt(def) => loop(ss, dict, list_vt_append(list_vt_reverse(def), exp))
				| ~None_vt() => (
					expression_free(exp);
					None_vt()
				)
			)
			// TODO See if its possible to reverse exp as we're iterating
			// the skeleton data structure for performance, instead of
			// reversing it here
			| list_vt_nil() => Some_vt(list_vt_reverse(exp))
	in
		loop(ske, dict, exp)
	end


fun read_file(name: string): void =
	let
		val name = "main.dats"
		val file_ref = fileref_open_opt(name, file_mode_r)
	in
		case+ file_ref of
		| ~None_vt() => println!("File ", name, " does not exist")
		| ~Some_vt(file) =>
			let
				implement fileref_get_word$isalpha<>(c) =
					not (c = ' ' || c = '\t' || c = '\n' || c = '\v' || c = '\f' || c = '\r')

				val word = fileref_get_word(file)
				val () = println!(word)
				val () = free(word)
				val word = fileref_get_word(file)
			in
				println!(word);
				free(word);
				close(file)
			end
	end

// overload free with option_vt_free
