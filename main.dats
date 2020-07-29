#include "share/atspre_staload.hats"
// #define ATS_DYNLOADFLAG 0

(*
	TODO: for every function that uses list_vt_reverse, implement the tail recursion using
	a pointer for the tail of the auxiliary list and change it every iteration to the newly
	created node. This will aliviate the memory usage and the time it takes to reduce expressions.
*)

(*
	The dependency (libgmp for ATS) was missing a definition in CATS/gmp.cats:
	#define atscntrb_gmp_mpz_set_str mpz_set_str
*)

staload "contrib/atscntrb/atscntrb-hx-libgmp/SATS/gmp.sats"

staload "./dictionary.sats"
staload "./pattern.sats"
staload "./phrase.sats"
staload "./rule.sats"
staload "./skeleton.sats"
staload "./stack.sats"
staload "./stack.dats"	// cause templates
staload "./string.sats"

overload close with fileref_close
overload is_some with option_vt_is_some

macdef rule_def = ":"
macdef rule_red = "=>"
macdef rule_end = ";"

viewtypedef Grammar = @[Rule][12]

#define EXP_VOID 0
#define EXP_NUM 1
#define EXP_STR 2
#define EXP_PAT 3
#define EXP_SKE 4
#define EXP_RUL 5

dataviewtype exp(int) =
	| exp_void(EXP_VOID)
	| exp_num(EXP_NUM) of int // TODO since gmp integers are used, replace this int with a mpz integer
	| exp_str(EXP_STR) of String
	| exp_pat(EXP_PAT) of Pattern
	| exp_ske(EXP_SKE) of Skeleton
	| exp_rul(EXP_RUL) of Rule

viewtypedef Exp = [n: nat] exp(n)

#define :: list_vt_cons


fn {a, b: viewt@ype} fmap_option_vt(f: a -> b, x: Option_vt(a)): Option_vt(b) =
	case+ x of
	| ~None_vt() => None_vt()
	| ~Some_vt(v) => Some_vt(f(v))

// <$> breaks the ATS compiler so...
infixr 50 <!>
overload <!> with fmap_option_vt

// This is probably not the correct type defintion for a parser but I am not an expert, specially
// given the fact that this has to work with linear streams
viewtypedef Parser(a: viewt@ype) = stream_vt(String) -> Option_vt(@(a, stream_vt(String)))
viewtypedef ParserT(a: viewt@ype) = stream_vt(String) -> a

extern castfn sz2i {n: int} (x: ssize_t(n)): int(n)
extern fun atoi(s: !String): int = "mac#"


// Checks if all the character of a string are digits
fun string_isdigit(s: !String): bool =
	let
		val n = atoi(s)
	in
		if (n = 0) * (s[0] != '0') then
			false
		else
			true
	end


// The mpz* related functions that operate on gmp number consume the linear resources but they
// don't really free the memory associated with them because the arguments are heap allocated
// strings and the function expects stack allocated ones... so "unsafe" operations are needed

// These are probably the most ATS looking functions in the whole project right now

// TODO implement these with a macro or in any other way really

fn intr_add(op1: String, op2: String): Option_vt(Phrase) =
	if string_isdigit(op1) * string_isdigit(op2) then
		let
			val op1cp = decode($vcopyenv_vt(op1))
			val op2cp = decode($vcopyenv_vt(op2))
			var i1: mpz
			val () = mpz_init(i1)
			var i2: mpz
			val () = mpz_init(i2)
			val res1 = mpz_set_str(i1, strnptr2string(op1), 10)
			val res2 = mpz_set_str(i2, strnptr2string(op2), 10)
			val () = string_free($UNSAFE.castvwtp0{String}(op1cp))
			val () = string_free($UNSAFE.castvwtp0{String}(op2cp))
			val () = mpz_add(i1, i2)
			val res = strptr2strnptr(mpz_get_str_null(10, i1))
			val () = assertloc(length(res) > 0)
			val () = assertloc(strnptr_isnot_null(res))
		in
			mpz_clear(i1);
			mpz_clear(i2);
			Some_vt($list_vt{String}(res))
		end
	else (
		gfree(op1);
		gfree(op2);
		None_vt()
	)

fn intr_mult(op1: String, op2: String): Option_vt(Phrase) =
	if string_isdigit(op1) * string_isdigit(op2) then
		let
			val op1cp = decode($vcopyenv_vt(op1))
			val op2cp = decode($vcopyenv_vt(op2))
			var i1: mpz
			val () = mpz_init(i1)
			var i2: mpz
			val () = mpz_init(i2)
			val res1 = mpz_set_str(i1, strnptr2string(op1), 10)
			val res2 = mpz_set_str(i2, strnptr2string(op2), 10)
			val () = string_free($UNSAFE.castvwtp0{String}(op1cp))
			val () = string_free($UNSAFE.castvwtp0{String}(op2cp))
			val () = mpz_mul(i1, i2)
			val res = strptr2strnptr(mpz_get_str_null(10, i1))
			val () = assertloc(length(res) > 0)
			val () = assertloc(strnptr_isnot_null(res))
		in
			mpz_clear(i1);
			mpz_clear(i2);
			Some_vt($list_vt{String}(res))
		end
	else (
		gfree(op1);
		gfree(op2);
		None_vt()
	)

fn intr_lt(op1: String, op2: String): Option_vt(Phrase) =
	if string_isdigit(op1) * string_isdigit(op2) then
		let
			val op1cp = decode($vcopyenv_vt(op1))
			val op2cp = decode($vcopyenv_vt(op2))
			var i1: mpz
			val () = mpz_init(i1)
			var i2: mpz
			val () = mpz_init(i2)
			val res1 = mpz_set_str(i1, strnptr2string(op1), 10)
			val res2 = mpz_set_str(i2, strnptr2string(op2), 10)
			val () = string_free($UNSAFE.castvwtp0{String}(op1cp))
			val () = string_free($UNSAFE.castvwtp0{String}(op2cp))
			val res = (
				if mpz_cmp(i1, i2) < 0 then
					string_new("true")
				else
					string_new("false")
			): String
		in
			mpz_clear(i1);
			mpz_clear(i2);
			Some_vt($list_vt{String}(res))
		end
	else (
		gfree(op1);
		gfree(op2);
		None_vt()
	)

// Checks if a phrase is an intrinsic in a very primitive way
fn check_intrinsics {n: int | n > 0} (ls: phrase(n)): Option_vt(Phrase) =
	let
		val+ ~list_vt_cons(head, tail) = ls
	in
		ifcase
		| head = "$add" => (
			gfree(head);
			if length(tail) = 2 then
				let
					val+ ~list_vt_cons(op1, tail) = tail
					val+ ~list_vt_cons(op2, ~list_vt_nil()) = tail
				in
					intr_add(op1, op2)
				end
			else (
				gfree(tail);
				None_vt()
			)
		)
		| head = "$mult" => (
			gfree(head);
			if length(tail) = 2 then
				let
					val+ ~list_vt_cons(op1, tail) = tail
					val+ ~list_vt_cons(op2, ~list_vt_nil()) = tail
				in
					intr_mult(op1, op2)
				end
			else (
				gfree(tail);
				None_vt()
			)
		)
		| head = "$lt" => (
			gfree(head);
			if length(tail) = 2 then
				let
					val+ ~list_vt_cons(op1, tail) = tail
					val+ ~list_vt_cons(op2, ~list_vt_nil()) = tail
				in
					intr_lt(op1, op2)
				end
			else (
				gfree(tail);
				None_vt()
			)
		)
		| _ => (
			gfree(head);
			gfree(tail);
			None_vt()
		)
	end

// Checks if a dictionary contains the definition of a specific symbol and returns it
fun lookup(symbol: !String, dict: !Dictionary): Option_vt(Phrase) =
	// It's very important to copy the expression in case there are more than one holes that refer
	// to the same pattern variable. For example: ?x => :x :x ;
	case+ dict of
	| list_vt_cons(t, ds) when t.0 = symbol => Some_vt(gcopy(t.1))
	| list_vt_cons(_, ds) => lookup(symbol, ds)
	| list_vt_nil() => None_vt()


// Returns (if successful) a pair containing a dictionary and the tail of the expression that was not matched
// This is the heart of the whole program and it is a very complicated piece of code
// TODO: ph should be a reference, in case of failure (None_vt()), it should remain intact
// if match was successful, ph should point to its tail
fun match(ph: Phrase, pat: !Pattern): Option_vt(@(Dictionary, Phrase)) =
	let
		fun match_loop {n: nat} (pat: !Pattern, ph: Phrase, dict: dictionary(n)): Option_vt(@(Dictionary, Phrase)) = (
			case+ pat of
			| pat_symbol(s)::ps => (
				case+ ph of
				| ~x::xs when x = s => (
					gfree(x);
					match_loop(ps, xs, dict)
				)
				| _ => (
					gfree(ph);
					gfree(dict);
					None_vt()
				)
			)

			| pat_atom(a)::ps => (
				case+ ph of
				| ~x::xs =>
					let
						val opt = lookup(a, dict)
					in
						case+ opt of
						// If the symbol is not in the dictionary, add it
						| ~None_vt() => match_loop(ps, xs, list_vt_cons((gcopy(a), x::list_vt_nil()), dict))
						// If the symbol is defined, compare the definitions and assert they are the same
						| ~Some_vt(def) =>
							let
								val def' = $list_vt{String}(x)
								val eq = def = def'
							in
								gfree(def);
								gfree(def');

								if eq then
									match_loop(ps, xs, dict)
								else (
									gfree(xs);
									gfree(dict);
									None_vt()
								)
							end
					end
				| _ => (
					gfree(ph);
					gfree(dict);
					None_vt()
				)
			)

			| pat_under()::ps => (
				case+ ph of
				| ~x::xs => (
					gfree(x);
					match_loop(ps, xs, dict)
				)
				| _ => (
					gfree(ph);
					gfree(dict);
					None_vt()
				)
			)

			| pat_bal(_)::ps => (
				gfree(ph);
				gfree(dict);
				None_vt()
			)

			// These are the "base" cases of the mult and ... patterns, successful recursive calls to match
			// that handle these patterns will end here
			| pat_mult(m)::list_vt_nil() => Some_vt(@(list_vt_cons(@(gcopy(m), ph), dict), list_vt_nil))

			| pat_ellip()::list_vt_nil() => (
				gfree(ph);
				Some_vt(@(dict, list_vt_nil))
			)

			| p::_ => (
				let
					// This function examines the pattern to check for a delimiter and splits it in two
					// at that specific symbol. XXX the case [1] can be removed if everything is handled
					// from within this function and thus speeding up the program
					fun create_subpattern {n: nat | n > 0} (pat: !Pattern, temp: pattern(n)): [m: int | m > 0] (pattern(m), Pattern) =
						// TODO handle here the case for the '_' and the '...'
						case+ pat of
						| list_vt_nil() => (temp, list_vt_nil())
						| list_vt_cons(pat_symbol(x), xs) => (list_vt_cons(pat_symbol(gcopy(x)), temp), pattern_copy(xs))
						| list_vt_cons(pat_bal(x), xs) => (list_vt_cons(pat_bal(gcopy(x)), temp), pattern_copy(xs))
						// Don't add successive mults without a proper delimiter as they are ambiguous
						| list_vt_cons(pat_mult(_), xs) => create_subpattern(xs, temp)
						| list_vt_cons(pat_ellip(), xs) => create_subpattern(xs, temp)
						| list_vt_cons(p, xs) => create_subpattern(xs, list_vt_cons(gcopy(p), temp))

					// Head could be multiple elements, not just one
					val+ @(pat_head, pat_tail) = create_subpattern(pat, $list_vt(gcopy(p)))
				in
					// XXX [1]
					case+ pat_head of
					// If the last (first, as it is reversed) element in the subpattern is a symbol
					// then find it in the phrase and cut the phrase at that position.
					| list_vt_cons(pat_symbol(last), cs) =>
						let
							fun create_subphrase(ph: Phrase, temp: Phrase, last: !String): @(Phrase, Phrase) =
								case+ ph of
								| ~list_vt_nil() => (temp, list_vt_nil())
								| ~list_vt_cons(x, xs) when x = last => (list_vt_cons(x, temp), xs)
								| ~list_vt_cons(x, xs) => create_subphrase(xs, list_vt_cons(x, temp), last)

							val+ @(ph_head, ph_tail) = create_subphrase(ph, list_vt_nil, last)

							implement list_vt_app$fwork<@(String, Phrase)>(t) = t.1 := list_vt_reverse(t.1)
							val () = list_vt_app(dict)


							val opt = match_loop(pat_head, ph_head, dict)
						in
							gfree(pat_head);

							case+ opt of
							| ~Some_vt(@(d,t)) =>
								let
									// d is the resulting dictionary from matching the subphrase that was cut
									// t has to be empty
									// val () = assertloc(length(d) > 0)
									val () = assertloc(length(t) = 0)

									// Since everything was reversed, definitions within the dictionary that
									// were created in the recursive call to match are also reversed so they
									// have to be reversed again
									// implement list_vt_app$fwork<@(String, Phrase)>(t) = t.1 := list_vt_reverse(t.1)
									val () = list_vt_app(d)

									// val dict = list_vt_append(d, dict)
									val res = match_loop(pat_tail, ph_tail, d)	// XXX not tail recursive
								in
									gfree(pat_tail);
									gfree(t);
									res
								end
							| ~None_vt() => (
								gfree(pat_tail);
								gfree(ph_tail);
								//gfree(dict);
								//stack_free(stk);
								None_vt()
							)
						end
					// TODO copypaste the match for pat_bal()
					// | list_vt_cons(pat_bal(last), _) =>

					// If the last element was not a symbol, just reverse the phrase and match
					// No recursive call is needed
					| list_vt_cons(_, _) =>
						let
							val () = assertloc(length(pat_tail) = 0)

							val rev = list_vt_reverse(ph)
							val- ~Some_vt(@(d, t)) = match(rev, pat_head)

							val () = assertloc(length(d) > 0)
							val () = assertloc(length(t) = 0)

							// Just like the other case, reverse the definitions in the dictionary
							implement list_vt_app$fwork<@(String, Phrase)>(t) = t.1 := list_vt_reverse(t.1)
							val () = list_vt_app(d)

							val dict = list_vt_append(d, dict)
						in
							gfree(pat_tail);
							gfree(pat_head);
							// Unlike the previous case, the phrase to be reduced has no tail since it
							// wasn't cut because no delimiter symbol was found, so there's no recursive
							// call here
							Some_vt(@(dict, t))
						end
				end
			)

			// If the pattern is empty, any phrase will match it. Considering that it is impossible
			// to add a rule with an empty pattern, this branch will only be reached when the matcher
			// has been successful on every recursive call
			| list_vt_nil() => Some_vt(@(dict, ph))

			// | _ => (gfree(temp); gfree(ph); gfree(dict); None_vt())
		)
	in
		if length(ph) >= pattern_length(pat) then
			match_loop(pat, ph, dictionary_new())
		else (
			gfree(ph);
			None_vt()
		)
	end

extern fun reduce: (Phrase, !List_vt(Rule)) -> Phrase

// Creates a new phrase given a dictionary and the skeleton by substituting the "holes" with the
// definitions of their respective symbols in the dictionary
fn instantiate(dict: !Dictionary, ske: !Skeleton): Phrase =
	let
		val phr: Phrase = phrase_new()

		fun instantiate_loop(ske: !Skeleton, dict: !Dictionary, ph: Phrase): Phrase =
			case+ ske of
			| ske_symbol(s)::ss => instantiate_loop(ss, dict, ph') where {
				val ph' = list_vt_append(gcopy(s)::list_vt_nil, ph)
			}
			| ske_hole(s)::ss => (
				case+ lookup(s, dict) of
				// TODO way too many (two, to be exact) reverses
				| ~Some_vt(def) => instantiate_loop(ss, dict, list_vt_append(list_vt_reverse(def), ph))
				| ~None_vt() => (
					// This branch should never be executed as the possibility of a symbol used in the
					// skeleton that is not defined in the dictionary is inconceivable because the rule
					// is checked to be valid during parsing
					gfree(ph);
					undefined()
				)
			)
			// TODO See if its possible to reverse ph as we're iterating
			// the skeleton data structure for performance, instead of
			// reversing it here
			| _ => list_vt_reverse(ph)
	in
		instantiate_loop(ske, dict, phr)
	end

fn option_vt_print(x: !Option_vt(int)): void =
	case+ x of
	| Some_vt(f) => (print("Some "); print(f))
	| None_vt() => print("None")

// If there are more tokens in the stream, return the token and the rest of the stream
fn {a: viewt@ype} stream_vt_uncons(st: stream_vt(a)): Option_vt(@(a, stream_vt(a))) =
	let
		val s = !st
	in
		case+ s of
		| ~stream_vt_cons(x, xs) => Some_vt(@(x, xs))
		| ~stream_vt_nil() => None_vt()
	end

// Turns a string into an integer
fn string2int {m: nat | m > 0} (s: strnptr11(m)): Option_vt(int) =
	let
		val len: int(m) = sz2i(length(s))
		fun loop {n: nat | n < m} (s: !strnptr11(m), i: int(n)): bool =
			if isdigit(strnptr_get_at_size(s, i2sz(i))) then
				if i + 1 < len then
					loop(s, i + 1)
				else
					true
			else
				false
	in
		if loop(s, 0) then
			let
				val n = atoi(s)
			in
				strnptr_free(s);
				Some_vt(n)
			end
		else (
			strnptr_free(s);
			None_vt()
		)
	end

// Parses any string
extern fn parse_string: Parser(exp(EXP_STR))
implement parse_string(st) =
	let
		val st' = stream_vt_uncons<String>(st)
	in
		case+ st' of
		| ~Some_vt(t) => Some_vt(@(exp_str(t.0), t.1))
		| ~None_vt() => None_vt()
	end

// Tries to parse a token and succeedes if the token matches the given string
fn parse_string_matching {n: nat | n > 0} (st: stream_vt(String), match: string(n)): Option_vt(@(exp(EXP_STR), stream_vt(String))) =
	let
		val st = stream_vt_uncons<String>(st)
	in
		case+ st of
		| ~Some_vt(t) =>
			let
				val st = t.1
				val s = t.0
			in
				if s = match then (
					Some_vt(@(exp_str(s), st))
				) else (
					stream_vt_free(st);
					strnptr_free(s);
					None_vt()
				)
			end
		| ~None_vt() => None_vt()
	end

// Tries to parse a number and succeedes if the token is a valid number (ONLY digits)
extern fn parse_int: Parser(exp(EXP_NUM))
implement parse_int(st) =
	let
		val st' = stream_vt_uncons<String>(st)
	in
		case+ st' of
		| ~Some_vt(t) when length(t.0) > 0 =>
			let
				val t_st: stream_vt(String) = t.1
				val t_s = t.0
				val n_opt = string2int(t_s)
			in
				case+ n_opt of
				| ~Some_vt(n) => Some_vt(@(exp_num(n), t_st))
				| ~None_vt() => (
					stream_vt_free(t_st);
					None_vt()
				)
			end
		| ~Some_vt(t) => (
			strnptr_free(t.0);
			stream_vt_free(t.1);
			None_vt()
		)
		| ~None_vt() => None_vt()
	end

// Parses a whole pattern
extern fn parse_pattern: Parser(exp(EXP_PAT))
implement parse_pattern(st) =
	let
		fun loop {n: nat} (st: stream_vt(String), p: pattern(n)): Option_vt(@(exp(EXP_PAT), stream_vt(String))) =
			let
				val st = stream_vt_uncons<String>(st)
			in
				case+ st of
				| ~None_vt() => (
					pattern_free(p);
					None_vt()
				)
				| ~Some_vt(t) =>
					let
						val st = t.1
						val s = t.0
					in
						if s = rule_red then (
							strnptr_free(s);
							Some_vt(@(exp_pat(list_vt_reverse(p)), st))
						) else (
							loop(st, list_vt_cons(pat_from_string(s), p))
						)
					end
			end
	in
		loop(st, $list_vt{Pat}())
	end

// Parses a whole skeleton
extern fn parse_skeleton: Parser(exp(EXP_SKE))
implement parse_skeleton(st) =
	let
		fun loop {n: nat} (st: stream_vt(String), sk: skeleton(n)): Option_vt(@(exp(EXP_SKE), stream_vt(String))) =
			let
				val st = stream_vt_uncons<String>(st)
			in
				case+ st of
				| ~None_vt() => (
					skeleton_free(sk);
					None_vt()
				)
				| ~Some_vt(t) =>
					let
						val st = t.1
						val s = t.0
					in
						if s = rule_end then (
							strnptr_free(s);
							Some_vt(@(exp_ske(list_vt_reverse(sk)), st))
						) else (
							loop(st, list_vt_cons(ske_from_string(s), sk))
						)
					end
			end
	in
		loop(st, $list_vt{Ske}())
	end

// These are the characters that act as separators between tokens
implement fileref_get_word$isalpha<>(c) =
	not (c = ' ' || c = '\t' || c = '\n' || c = '\v' || c = '\f' || c = '\r')

// Turns a file into a stream (or lazily evaluated list)
fun streamize_fileref_word(file: FILEref): stream_vt(String) =
	$ldelay(
		if fileref_is_eof(file) then
			stream_vt_nil()
		else
			let
				val st = strptr2strnptr(fileref_get_word(file))
			in
				if strnptr_isnot_null(st) * (strnptr_length(st) > 0) then
					stream_vt_cons(st, streamize_fileref_word(file))
				else (
					strnptr_free(st);
					stream_vt_nil()
				)
			end
	)



fn print_ex(e: !Exp): void =
	case+ e of
	| exp_void() => ()
	| exp_num(n) => print(n)
	| exp_str(s) => print(s)
	| exp_pat(p) => pattern_print(p)
	| exp_ske(s) => skeleton_print(s)
	| exp_rul(r) => rule_print(r)

fn free_ex(e: Exp): void =
	case+ e of
	| ~exp_void() => ()
	| ~exp_num(n) => ()
	| ~exp_str(s) => gfree(s)
	| ~exp_pat(p) => gfree(p)
	| ~exp_ske(s) => gfree(s)
	| ~exp_rul(r) => gfree(r)

macdef parse_keyword = parse_string_matching

// The delicate art of working with linear streams
// This function performs an uncons on a stream. If there is a token, copies it and returns that token
// and the stream WITH that token, it (semantically) does not remove the head of the stream
fn stream_vt_peek(st: stream_vt(String)): @(Option_vt(String), stream_vt(String)) =
	let
		val s = !st
	in
		case+ s of
		| ~stream_vt_nil() => @(None_vt(), $ldelay(stream_vt_nil()))
		| ~stream_vt_cons(x, xs) => @(Some_vt(gcopy(x)), $ldelay(stream_vt_cons(x, xs), (~xs; gfree(x))))
	end


extern fun {a: viewt@ype} option_vt_freelin$clear(x: &a >> a?):<!wrt> void


// This does not free any memory
fun {a:viewt@ype} forget (x: &a >> a?): void = let prval () = $UNSAFE.castvwtp2void(x) in end



implement {a} option_vt_freelin$clear(x) = $effmask_all(forget<a>(x))


fun {a: viewt@ype} option_vt_freelin(x: Option_vt(a)): void =
	case+ x of
	| ~None_vt() => ()
	| @Some_vt(c) => (
		option_vt_freelin$clear(c);
		free@{a}(x)
	)


extern fn parse_rule: Parser(exp(EXP_RUL))

// Don't look
// Parses a whole rule ( <level> <precedence> <name> : <pattern> => <skeleton> ; )
implement parse_rule(st) =
	let
		val level = parse_int(st)
	in
		case+ level of
		| ~None_vt() => (/*println!("Expected rule level (integer)");*/ None_vt())
		| ~Some_vt(t) =>
			let
				val l = t.0
				val prec = parse_int(t.1)
			in
				case+ prec of
				| ~None_vt() => (println!("Expected rule precedence (integer)"); free_ex(l); None_vt())
				| ~Some_vt(t) =>
					let
						val p = t.0
						val name = parse_string(t.1)
					in
						case+ name of
						| ~None_vt() => (println!("Expected rule name"); free_ex(l); free_ex(p); None_vt())
						| ~Some_vt(t) =>
							let
								val n = t.0
								val colon = parse_keyword(t.1, rule_def)
							in
								case+ colon of
								| ~None_vt() => (println!("Expected colon (:)"); free_ex(l); free_ex(p); free_ex(n); None_vt())
								| ~Some_vt(t) =>
									let
										val+ ~exp_str(col) = t.0
										val patt = parse_pattern(t.1)
									in
										strnptr_free(col);
										case+ patt of
										| ~None_vt() => (free_ex(l); free_ex(p); free_ex(n); None_vt())
										| ~Some_vt(t) =>
											let
												val+ ~exp_pat(pt) = t.0
												val skel = parse_skeleton(t.1)
											in
												case+ skel of
												| ~None_vt() => (free_ex(l); free_ex(p); free_ex(n); pattern_free(pt); None_vt())
												| ~Some_vt(t) =>
													let
														val+ ~exp_num(l) = l
														val+ ~exp_num(p) = p
														val+ ~exp_str(n) = n
														val+ ~exp_ske(sk) = t.0
														val rule = @{
															level = l,
															precedence = p,
															name = n,
															pattern = pt,
															skeleton = sk
														}: Rule
													in
														Some_vt(@(exp_rul(rule), t.1))
													end
											end
									end
							end
					end

			end
	end

// Filters a list of rules by their level. If one rule matches the given level it is
// taken out and added to a list containing all the rules that match
fn filter_rules(rules: &List_vt(Rule) >> _, level: int): List_vt(Rule) =
	let
		fun loop {n: nat} (rules: &List_vt(Rule) >> _, temp: list_vt(Rule, n)): List_vt(Rule) =
			case+ rules of
			| ~list_vt_cons(r, rs) when r.level = level =>
				let
					val temp = list_vt_cons(r, temp)
				in
					rules := rs;
					loop(rules, temp)
				end
			| list_vt_cons(r, rs) => loop(rules, temp)
			| list_vt_nil() => list_vt_reverse(temp)
	in
		loop(rules, list_vt_nil())
	end

// Adds a new rule to a list of rule while maintaining the precedence
fun add_rule {n: nat} (rules: list_vt(Rule, n), rule: Rule): list_vt(Rule, n + 1) =
	case+ rules of
	| list_vt_cons(r, rs) when rule.precedence > r.precedence => list_vt_cons(rule, rules)
	| ~list_vt_cons(r, rs) => list_vt_cons(r, add_rule(rs, rule))
	| ~list_vt_nil() => $list_vt{Rule}(rule)

// Skips (and frees) all tokens until a given string is matched
fun stream_vt_skip_until {n: int | n > 0} (st: stream_vt(String), until: string(n)): Option_vt(stream_vt(String)) =
	let
		val opt = stream_vt_uncons<String>(st)
	in
		case+ opt of
		| ~None_vt() => None_vt()
		| ~Some_vt(t) =>
			let
				val s = t.0
				val st = t.1
				val b = s = until
			in
				gfree(s);
				if b then
					Some_vt(st)
				else
					stream_vt_skip_until(st, until)
			end
	end

// Parses a block comment ( /* ... */ )
extern fun parse_comment: Parser(exp(EXP_VOID))
implement parse_comment(st) = (lam(x) => @(exp_void(), x)) <!> stream_vt_skip_until(st, "*/")


/*
TODO figure this one
extern fun parse_comment_endline: Parser(exp(EXP_VOID))
implement parse_comment_endline(st) =
	let
		implement fileref_get_word$isalpha<>(c) =
			not (c = ' ' || c = '\t' || c = '\v' || c = '\f' || c = '\r')
	in
		(lam(x) => @(exp_void(), x)) <!> stream_vt_skip_until(st, "\n")
	end
*/

// Parses a file containing either rules or comments.
// Comments can ONLY be located outside of a rule, if the tokens "/*" or "*/" are found within a
// rule (name, pattern or skeleton) it will be interpreted as a regular symbol
extern fun parse_file: ParserT(List_vt(Rule))
implement parse_file(st) =
	let
		// TODO change this to a Optional type instead of a list as return value?
		fun loop {n: nat} (st: stream_vt(String), rules: list_vt(Rule, n)): List_vt(Rule) =
			let
				val+ (t, st) = stream_vt_peek(st)
			in
				case+ t of
				| ~None_vt() => (~st; rules)
				| ~Some_vt(symbol) when symbol = "/*" =>
					let
						val opt = parse_comment(st)
					in
						gfree(symbol);
						case+ opt of
						| ~None_vt() => rules
						| ~Some_vt(@(~exp_void(), st)) => loop(st, rules)
					end
				/*
				| ~Some_vt(symbol) when symbol = "//" =>
					let
						val opt = parse_comment_endline(st)
					in
						gfree(symbol);
						case+ opt of
						| ~None_vt() => rules
						| ~Some_vt(@(~exp_void(), st)) => loop(st, rules)
					end
				*/
				| ~Some_vt(symbol) => (
					let
						val opt = parse_rule(st)
						implement list_vt_freelin$clear<Rule>(r) = $effmask_all(rule_free(r))
					in
						gfree(symbol);
						case+ opt of
						| ~None_vt() => (
							gprintln!("\033[0;31mError parsing a rule\033[0m");
							list_vt_freelin(rules);
							list_vt_nil()
						)
						| ~Some_vt(t) =>
							let
								val+ ~exp_rul(r) = t.0
								val st = t.1
							in
								if rule_is_valid(r) then
									loop(st, add_rule(rules, r))
								else (
									// If a rule is not valid, undo everything
									gprintln!("\033[0;31mRule: ", r, " is invalid\033[0m");
									gfree(r);
									stream_vt_free(st);
									list_vt_freelin(rules);
									list_vt_nil()
								)
							end
					end
				)

			end
	in
		loop(st, $list_vt{Rule}())
	end

// Reduces a phrase in a VERY recursive fashion
implement reduce(ph, rules) =
	let
		val () = gprintln!(ph)
		val (pf | all_rules) = decode($vcopyenv_vt(rules))

			// Try matching the expression against the rule r
			fun try_rule(ph: Phrase, head: Phrase, rule: !Rule): Option_vt(Phrase) =
				case+ ph of
				| ~list_vt_nil() => (
					// since any empty expresssion matches any rules, don't try to match it
					gfree(head);
					None_vt()
				)
				| list_vt_cons(_, _) =>
					let
						val match_opt = match(gcopy(ph), rule.pattern)
					in
						case+ match_opt of
						| ~None_vt() => try_rule(xs, list_vt_extend(head, x), rule) where {
							val+ ~list_vt_cons(x, xs) = ph
						}
						| ~Some_vt(@(dict, tail)) =>
							// The match was successful
							let
								val body = instantiate(dict, rule.skeleton)
							in
								gfree(ph);
								gfree(dict);
								let
									val (pf | all_rules) = decode($vcopyenv_vt(all_rules))
									val reduced_body = reduce(body, all_rules)
									val head_body = list_vt_append(head, reduced_body)
									val final = list_vt_append(head_body, tail)
									var res = reduce(final, all_rules)
									prval () = pf(all_rules)
								in
									Some_vt(res)
								end
							end
					end

			fun try_rules(ph: Phrase, rules: !List_vt(Rule)): Phrase =
				case+ rules of
				| list_vt_nil() => ph
				| list_vt_cons(r, rs) =>
					let
						val opt = try_rule(gcopy(ph), list_vt_nil(), r)
					in
						case+ opt of
						| ~Some_vt(p) => (gfree(ph); p)
						| ~None_vt() => try_rules(ph, rs)
					end



		prval () = pf(all_rules)
	in
		if length(ph) > 0 then
			let
				val+ list_vt_cons(head, _) = ph
			in
				if head[0] = '$' then
					let
						val cp = gcopy(ph)
						val opt = check_intrinsics(cp)
					in
						case+ opt of
						| ~None_vt() => try_rules(ph, rules)
						| ~Some_vt(res) => (
							gfree(ph);
							res
					)
					end
				else
					try_rules(ph, rules)
			end
		else
			ph
	end

implement main0(argc, argv) =
	let
		val file =
			if argc > 1 then
				let
					val file_opt = fileref_open_opt(argv[1], file_mode_r)
				in
					case+ file_opt of
					| ~None_vt() => stdin_ref
					| ~Some_vt(f) => f
				end
			else
				stdin_ref

		val stream = streamize_fileref_word(file)

		implement list_vt_freelin$clear<Rule>(r) = $effmask_all(rule_free(r))

		// val grammar = some array of rules

		var rules = parse_file(stream)

		val level_0 = filter_rules(rules, 0)
		val level_1 = filter_rules(rules, 1)

		// val grammar = arrayptr_make_uninitized<List_vt(Rule)>(i2sz 12)
		// val () = arrayptr_set_at_gint(grammar, 0, level_0)
		// implement array_uninitize$clear<List_vt(Rule)>(i, x) = list_vt_freelin<Rule>(x)
		// val () = arrayptr_freelin(grammar, i2sz 12)
		val init0 = $list_vt{String}(string_new("main"))
		val init1 = $list_vt{String}(string_new("main"))

		// Phrase reduction loop
		val () = println!("Reductions:")
		val exp0 = reduce(init0, level_0)
		val exp1 = reduce(init1, level_1)
	in
		gprintln!("\nFinal expression\n0: ", exp0, "\n1: ", exp1);
		list_vt_freelin(rules);
		gfree(exp0);
		gfree(exp1);
		list_vt_freelin(level_0);
		list_vt_freelin(level_1);

		close(file)
	end
