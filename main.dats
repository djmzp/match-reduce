#include "share/atspre_staload.hats"

// #define ATS_DYNLOADFLAG 0

staload "dictionary.sats"
staload "expression.sats"
staload "pattern.sats"
staload "skeleton.sats"

overload close with fileref_close

/*
	100 r_sum: ?x + ?y => $sum :x :y ;
*/

viewtypedef Rule = @{
	precedence = int,
	name = string,
	pattern = Pattern,
	skeleton = Skeleton
}

#define :: list_vt_cons

fun lookup(symbol: !Strptr1, dict: !Dictionary): Option_vt(Expression) =
	case+ dict of
	| list_vt_cons(x, ds) when compare_strptr_strptr(x.0, symbol) = 0 =>
		Some_vt(expression_copy(x.1))
	| list_vt_cons(_, ds) => lookup(symbol, ds)
	| list_vt_nil() => None_vt()

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

#include "tests.dats"

implement main0() = run_tests()
