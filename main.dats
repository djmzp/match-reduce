#include "share/atspre_staload.hats"
// #define ATS_DYNLOADFLAG 0

staload "./dictionary.sats"
staload "./pattern.sats"
staload "./phrase.sats"
staload "./rule.sats"
staload "./skeleton.sats"
staload "./string.sats"

overload close with fileref_close

viewtypedef Grammar = @[Rule][12]

#define EXP_NUM 0
#define EXP_STR 1
#define EXP_PAT 2
#define EXP_SKE 3
#define EXP_RUL 4

dataviewtype exp(int) =
	| num(EXP_NUM) of int
	| str(EXP_STR) of String
	| pat(EXP_PAT) of Pattern
	| ske(EXP_SKE) of Skeleton
	| rul(EXP_RUL) of Rule

viewtypedef Exp = [n: nat] exp(n)

#define :: list_vt_cons

fun lookup(symbol: !String, dict: !Dictionary): Option_vt(Phrase) =
	// It's very important to copy the expression in case there are more than one holes that refer
	// to the same pattern variable. For example: ?x => :x :x ;
	case+ dict of
	| list_vt_cons(t, ds) when compare(t.0, symbol) = 0 => Some_vt(gcopy(t.1))
	| list_vt_cons(_, ds) => lookup(symbol, ds)
	| list_vt_nil() => None_vt()

fn is_balanced {n: nat | n > 0} (ph: !Phrase, symbols: phrase(n)): bool =
	let
		val+ ~list_vt_cons(x, xs) = symbols
		val o = ocurrences(ph, x)

		fun loop(ph: !Phrase, symbols: Phrase): bool =
			case+ symbols of
			| ~list_vt_nil() => true
			| ~list_vt_cons(x, xs) =>
				let
					val ocur = ocurrences(ph, x)
				in
					gfree(x);
					if ocur = o then
						loop(ph, xs)
					else (
						gfree(xs);
						false
					)
				end
	in
		gfree(x);
		loop(ph, xs)
	end


// Returns (if successful) a pair containing a dictionary and the tail of the expression that was not matched
fn match(ph: Phrase, pat: !Pattern): Option_vt(@(Dictionary, Phrase)) =
	let
		val dict = dictionary_new();

		fun loop {n: nat} (pat: !Pattern, ph: Phrase, dict: dictionary(n), temp: Phrase): Option_vt(@(Dictionary, Phrase)) =
			// TODO change this case+ to pattern match only on the pattern
			case+ (pat, ph) of
			| (pat_symbol(s1)::ps, ~s2::es) when compare(s1, s2) = 0 => (
				gfree(s2);
				loop(ps, es, dict, temp)
			)
			| (pat_symbol(s1)::ps, s2::es) => (
				gfree(dict);
				gfree(ph);
				gfree(temp);
				None_vt()
			)/*
			| (pat_atom(s1)::ps, ~s2::es) => loop(ps, es, dict', temp) where {
				val dict' = list_vt_cons((strptr1_copy(s1), s2::list_vt_nil()), dict)
			}*/
			| (pat_atom(a)::ps, ~s2::es) => (
				let
					val def = lookup(a, dict)
				in
					case+ def of
					| ~None_vt() => loop(ps, es, list_vt_cons((string_copy(a), s2::list_vt_nil()), dict), temp)
					| ~Some_vt(s) =>
						let
							val d = $list_vt{String}(s2)
							val eq = s = d
						in
							gfree(d);
							gfree(s);

							if eq then
								loop(ps, es, dict, temp)
							else (
								gfree(temp);
								gfree(es);
								gfree(dict);
								None_vt()
							)
						end
				end
			)

			| (pat_mult(s1)::list_vt_nil(), _) => Some_vt(@(dict', list_vt_nil())) where {
				val () = gfree(temp)
				val dict' = list_vt_cons((gcopy(s1), ph), dict)
			}

			| (pat_mult(s1)::ps, list_vt_nil()) => (
				gfree(temp);
				gfree(dict);
				gfree(ph);
				None_vt()
			)

			| (pat_mult(s1)::pat_symbol(lookahead)::ps, ~s2::es) when compare(s2, lookahead) = 0 =>
			let
				val temp' = gcopy(temp)
				val () = gfree(temp)
				val () = string_free(s2)
				val dict' = list_vt_cons((gcopy(s1), temp'), dict)
			in
				loop(ps, es, dict', $list_vt{String}())
			end

			| (pat_mult(s1)::pat_symbol(lookahead)::ps, ~s2::es) =>
			let
				val tmp = list_vt_extend(temp, s2)
			in
				loop(pat, es, dict, tmp)
			end

			/*
			| (pat_mult(s1)::ps, ~s2::es) => (
				case+ ps of
				| pat_symbol(s)::pss when compare(s, s2) = 0 =>
					let
						val temp' = expression_copy(temp)
						val () = expression_free(temp)
						val () = gfree(s2)
						val dict' = list_vt_cons((gcopy(s1), temp'), dict)
					in
						loop(ps, es, dict', $list_vt{String}())
					end
				| pat_symbol(s)::pss =>
					let
						val tmp = list_vt_extend(temp, s2)
					in
						loop(pat, es, dict, tmp)
					end
				| pat_atom(a)::pss =>
					let
						val temp' = expression_copy(temp)
						val () = expression_free(temp)
						val () = gfree(s2)
						val temp = $list_vt{String}()
						val dict' = list_vt_cons((gcopy(s1), temp'), dict)
					in
						loop(ps, es, dict', temp)
					end
				| pat_mult(ss2)::pss =>
				let
					val temp' = expression_copy(temp)
					val () = expression_free(temp)
					val () = gfree(s2)
					val temp = $list_vt{String}()
					val dict' = list_vt_cons((gcopy(s1), temp'), dict)
				in
					loop(ps, es, dict', temp)
				end
				| _ => (expression_free(temp); gfree(s2); dictionary_free(dict); expression_free(es); None_vt())

			)
			*/


			| (list_vt_nil(), _) => (
				gfree(temp);
				Some_vt(@(dict, ph))
			)

			// If the expression is empty, it does not match anything because it will enter a loop
			| (_, ~list_vt_nil()) => (
				gfree(temp);
				gfree(dict);
				None_vt()
			)

			| (_, _) => (
				// Lets try to be positive
				// dictionary_free(dict);
				gfree(temp);
				Some_vt(@(dict, ph))
			)

	in
		loop(pat, ph, dict, phrase_new())
	end


// Is there any reason to keep the dictionary after instantiating an skeleton?
fn instantiate(dict: !Dictionary, ske: !Skeleton): Option_vt(Phrase) =
	let
		val phr: Phrase = phrase_new()

		fun loop(ske: !Skeleton, dict: !Dictionary, ph: Phrase): Option_vt(Phrase) =
			case+ ske of
			| ske_symbol(s)::ss => loop(ss, dict, ph') where {
				// XXX this used to be extend
				val ph' = list_vt_append(gcopy(s)::list_vt_nil, ph)
			}
			| ske_hole(s)::ss => (
				case+ lookup(s, dict) of
				// TODO way too many (two, to be exact) reverses
				| ~Some_vt(def) => loop(ss, dict, list_vt_append(list_vt_reverse(def), ph))
				| ~None_vt() => (
					gfree(ph);
					None_vt()
				)
			)
			// TODO See if its possible to reverse exp as we're iterating
			// the skeleton data structure for performance, instead of
			// reversing it here
			| list_vt_nil() => Some_vt(list_vt_reverse(ph))
	in
		loop(ske, dict, phr)
	end


extern castfn sz2i {n: int} (x: ssize_t(n)): int(n)

fn option_vt_print(x: !Option_vt(int)): void =
	case+ x of
	| Some_vt(f) => (print("Some "); print(f))
	| None_vt() => print("None")

extern fun atoi(s: !Strnptr): int = "mac#"

fn {a: viewt@ype} stream_vt_uncons(st: stream_vt(a)): Option_vt(@(a, stream_vt(a))) =
	let
		val s = !st
	in
		case+ s of
		| ~stream_vt_cons(x, xs) => Some_vt(@(x, xs))
		| ~stream_vt_nil() => None_vt()
	end

fn strnptr2int {m: nat | m > 0} (s: strnptr(m)): Option_vt(int) =
	let
		val len: int(m) = sz2i(length(s))
		fun loop {n: nat | n < m} (s: !strnptr(m), i: int(n)): bool =
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

fn parse_string(st: stream_vt(String)): Option_vt(@(exp(1), stream_vt(String))) =
	let
		val st' = stream_vt_uncons<String>(st)
	in
		case+ st' of
		| ~Some_vt(t) => Some_vt(@(str(t.0), t.1))
		| ~None_vt() => None_vt()
	end

fn parse_string_matching(st: stream_vt(String), match: string): Option_vt(@(exp(1), stream_vt(String))) =
	let
		val st = stream_vt_uncons<String>(st)
	in
		case+ st of
		| ~Some_vt(t) =>
			let
				val st = t.1
				val s = t.0
				val d = strnptr_copy(s)
				val e = strnptr2string(d)
				val eq = eq_string_string(e, match)
				val () = strptr_free($UNSAFE.castvwtp0{strptr} e)
			in
				if eq then (
					Some_vt(@(str(s), st))
				) else (
					stream_vt_free(st);
					strnptr_free(s);
					None_vt()
				)
			end
		| ~None_vt() => None_vt()
	end

fn parse_int(st: stream_vt(String)): Option_vt(@(exp(EXP_NUM), stream_vt(String))) =
	let
		val st' = stream_vt_uncons<String>(st)
	in
		case+ st' of
		| ~Some_vt(t) when length(t.0) > 0 =>
			let
				val t_st: stream_vt(String) = t.1
				val t_s: Strnptr = t.0
				val n_opt = strnptr2int(t_s)
			in
				case+ n_opt of
				| ~Some_vt(n) => Some_vt(@(num(n), t_st))
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

fn parse_pat(st: stream_vt(String)): Option_vt(@(exp(EXP_PAT), stream_vt(String))) =
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
						val d = strnptr_copy(s)
						val e = strnptr2string(d)
						val eq = eq_string_string(e, "=>")
						// So yeah... ATS allows a leak here. This cast has to be done
						val () = strptr_free($UNSAFE.castvwtp0{strptr}(e))
					in
						if eq then (
							strnptr_free(s);
							Some_vt(@(pat(list_vt_reverse(p)), st)) // Again... list_vt_reverse here too
						) else (
							loop(st, list_vt_cons(pat_from_string(s), p))
						)
					end
			end
	in
		loop(st, $list_vt{Pat}())
	end

fn parse_skeleton(st: stream_vt(String)): Option_vt(@(exp(EXP_SKE), stream_vt(String))) =
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
						val d = strnptr_copy(s)
						val e = strnptr2string(d)
						val eq = eq_string_string(e, ";")
						val () = strptr_free($UNSAFE.castvwtp0{strptr}(e))
					in
						if eq then (
							strnptr_free(s);
							Some_vt(@(ske(list_vt_reverse(sk)), st))
						) else (
							loop(st, list_vt_cons(ske_from_string(s), sk))
						)
					end
			end
	in
		loop(st, $list_vt{Ske}())
	end

fun streamize_fileref_word(file: FILEref): stream_vt(String) =
	$ldelay(
		if fileref_is_eof(file) then
			stream_vt_nil()
		else
			let
				implement fileref_get_word$isalpha<>(c) =
					not (c = ' ' || c = '\t' || c = '\n' || c = '\v' || c = '\f' || c = '\r')
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
	| num(n) => print(n)
	| str(s) => print(s)
	| pat(p) => pattern_print(p)
	| ske(s) => skeleton_print(s)
	| rul(r) => rule_print(r)

fn free_ex(e: Exp): void =
	case+ e of
	| ~num(n) => ()
	| ~str(s) => strnptr_free(s)
	| ~pat(p) => pattern_free(p)
	| ~ske(s) => skeleton_free(s)
	| ~rul(r) => rule_free(r)

fun free_exp(e: List_vt(Exp)): void =
	case+ e of
	| ~list_vt_cons(~num(_), es) => free_exp(es)
	| ~list_vt_cons(~str(s), es) => (strnptr_free(s); free_exp(es))
	| ~list_vt_cons(~pat(p), es) => (pattern_free(p); free_exp(es))
	| ~list_vt_cons(~ske(s), es) => (skeleton_free(s); free_exp(es))
	| ~list_vt_cons(~rul(r), es) => (rule_free(r); free_exp(es))
	| ~list_vt_nil() => ()

macdef parse_keyword = parse_string_matching

// The delicate art of working with linear streams
fn stream_vt_peek(st: stream_vt(String)): @(Option_vt(String), stream_vt(String)) =
	let
		val s = !st
	in
		case+ s of
		| ~stream_vt_nil() => @(None_vt(), $ldelay(stream_vt_nil()))
		| ~stream_vt_cons(x, xs) => @(Some_vt(gcopy(x)), $ldelay(stream_vt_cons(x, xs), (~xs; gfree(x))))
	end


// Don't look
fn parse_rule(st: stream_vt(String)): Option_vt(@(exp(4), stream_vt(String))) =
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
								val colon = parse_keyword(t.1, ":")
							in
								case+ colon of
								| ~None_vt() => (println!("Expected colon (:)"); free_ex(l); free_ex(p); free_ex(n); None_vt())
								| ~Some_vt(t) =>
									let
										val+ ~str(col) = t.0
										val patt = parse_pat(t.1)
									in
										strnptr_free(col);
										case+ patt of
										| ~None_vt() => (free_ex(l); free_ex(p); free_ex(n); None_vt())
										| ~Some_vt(t) =>
											let
												val+ ~pat(pt) = t.0
												val skel = parse_skeleton(t.1)
											in
												case+ skel of
												| ~None_vt() => (free_ex(l); free_ex(p); free_ex(n); pattern_free(pt); None_vt())
												| ~Some_vt(t) =>
													let
														val+ ~num(l) = l
														val+ ~num(p) = p
														val+ ~str(n) = n
														val+ ~ske(sk) = t.0
														val rule = @{
															level = l,
															precedence = p,
															name = n,
															pattern = pt,
															skeleton = sk
														}: Rule
													in
														Some_vt(@(rul(rule), t.1))
													end
											end
									end
							end
					end

			end
	end


fn try_rule(ph: !Phrase, rule: !Rule): Option_vt(Phrase) =
	let
		val copy = gcopy(ph)

		fun loop(ph: Phrase, rule: !Rule, tmp: Phrase): Option_vt(Phrase) =
			case+ ph of
			| ~list_vt_nil() => (gfree(tmp); None_vt())
			| list_vt_cons(p, ps) =>
				let
					val p = gcopy(p)
					val cp = gcopy(ps)
					val opt = match(ph, rule.pattern)
				in
					case+ opt of
					| ~None_vt() => loop(cp, rule, tmp) where {
						val tmp = list_vt_cons(p, tmp)
					}
					| ~Some_vt(t) =>
						let
							val dict = t.0
							val tail = t.1
							val final = instantiate(dict, rule.skeleton)
						in
							gfree(p);
							gfree(cp);
							dictionary_free(dict);
							case+ final of
							| ~None_vt() => (
								gfree(tmp);
								gfree(tail);
								None_vt()
							)
							| ~Some_vt(p) =>
								let
									val tail = list_vt_append(p, tail)
									val head = list_vt_reverse(tmp)
								in
									Some_vt(list_vt_append(head, tail))
								end

						end
				end
	in
		loop(copy, rule, phrase_new())
	end

fun try_rules(ph: !Phrase, rules: !List_vt(Rule)): Option_vt(@(String, Phrase)) =
	case+ rules of
	| list_vt_nil() => None_vt()
	| list_vt_cons(r, rs) =>
		let
			val name = gcopy(r.name)
			val opt = try_rule(ph, r)
		in
			case+ opt of
			| ~None_vt() => (
				gfree(name);
				try_rules(ph, rs)
			)
			| ~Some_vt(e) => Some_vt(@(name, e))
		end




fn filter_rules(rules: !List_vt(Rule), level: int): List_vt(Rule) =
	let
		fun loop {n: nat} (rules: !List_vt(Rule), ac: list_vt(Rule, n)): List_vt(Rule) =
			case+ rules of
			| list_vt_nil() => ac
			| list_vt_cons(r, rs) when r.level = level => loop(rs, list_vt_cons(rule_copy(r), ac))
			| list_vt_cons(_, rs) => loop(rs, ac)
	in
		list_vt_reverse(loop(rules, $list_vt{Rule}()))
	end


fun add_rule {n: nat} (rules: list_vt(Rule, n), rule: Rule): list_vt(Rule, n + 1) =
	case+ rules of
	| list_vt_cons(r, rs) when rule.precedence > r.precedence => list_vt_cons(rule, rules)
	| ~list_vt_cons(r, rs) => list_vt_cons(r, add_rule(rs, rule))
	| ~list_vt_nil() => $list_vt{Rule}(rule)


// Since comments are ignored, this function does not have to return a tuple
fun skip_comment(st: stream_vt(String)): Option_vt(stream_vt(String)) =
	let
		val opt = stream_vt_uncons<String>(st)
	in
		case+ opt of
		| ~None_vt() => None_vt()
		| ~Some_vt(t) =>
			let
				val s = t.0
				val st = t.1
				val b = s = "*/"
			in
				gfree(s);
				if b then
					Some_vt(st)
				else
					skip_comment(st)
			end
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

		// TODO This function is really bad now that rules are not the only thing that can be expected
		// inside a file. Change it so it's not so "rule-centric"
		fun read_rules {n: nat} (st: stream_vt(String), rules: list_vt(Rule, n)): List_vt(Rule) =
			let
				val @(t, st) = stream_vt_peek(st)
				val out = (
					case+ t of
					| ~None_vt() => parse_rule(st)
					| ~Some_vt(s) when s = "/*" =>
						(
							gfree(s);
							let
								val opt = skip_comment(st)
							in
								case+ opt of
								| ~None_vt() => None_vt()
								| ~Some_vt(st) => parse_rule(st)
							end
						)
					| ~Some_vt(s) => (gfree(s); parse_rule(st))
				): Option_vt(@(exp(4), stream_vt(String)))
			in
				case+ out of
				| ~None_vt() => rules
				| ~Some_vt(t) =>
					let
						val+ ~rul(r) = t.0
						val st: stream_vt(String) = t.1
					in
						if rule_is_valid(r) then
							read_rules(st, add_rule(rules, r))
						else (
							print!("Rule: ");
							rule_print(r);
							println!(" is not valid.");
							rule_free(r);
							read_rules(st, rules)
						)
					end
			end

		implement list_vt_freelin$clear<Rule>(r) = $effmask_all(rule_free(r))

		// val grammar = some array of rules

		val rules = read_rules(stream, $list_vt{Rule}())
		// val () = print_rules(rules)
		// val () = println!()
		val level_0 = filter_rules(rules, 0)
		val level_1 = filter_rules(rules, 1)
		// val grammar = arrayptr_make_uninitized<List_vt(Rule)>(i2sz 12)
		// val () = arrayptr_set_at_gint(grammar, 0, level_0)
		implement array_uninitize$clear<List_vt(Rule)>(i, x) = list_vt_freelin<Rule>(x)
		// val () = arrayptr_freelin(grammar, i2sz 12)
		val init0 = $list_vt{String}(string_new("main"))
		val init1 = $list_vt{String}(string_new("main"))

		// Expression reduction loop
		fun red_loop(ph: Phrase, rules: !List_vt(Rule)): Phrase =
			let
				val ph_opt = try_rules(ph, rules)
			in
				case+ ph_opt of
				| ~Some_vt(t) => (
					let
						val name = t.0
						val ph' = t.1
					in
						gprint(ph);
						println!();
						gfree(name);
						gfree(ph);
						red_loop(ph', rules)
					end
				)
				| ~None_vt() => ph
			end

		val () = println!("Reductions:")
		val exp0 = red_loop(init0, level_0)
		val exp1 = red_loop(init1, level_1)
	in
		println!("\nFinal expression:");
		list_vt_freelin(rules);
		print("0: ");
		gprint(exp0);
		println!();
		print("1: ");
		gprint(exp1);
		println!();
		gfree(exp0);
		gfree(exp1);
		list_vt_freelin(level_0);
		list_vt_freelin(level_1);
		close(file)
	end
