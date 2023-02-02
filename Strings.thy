theory Strings
  imports Core "strings/RegEx" "strings/Words" 
begin

(* 
This is the interface between SMT-LIB and the underlying the theory of strings.
It contains mappings from SMT-LIB predicates/functions to the corresponding formalization/implementation.

Predicates in SMT-LIB are defined over integers and string, whereas in the corresponding Isabelle
theories, they are defined naturally over natural number and string.
The conversion between integers and naturals as well as handling of edge cases 
(as explained in the SMT-LIB standard) is performed here.

Pure string predicates are defined in "strings/Words", regular expression in "strings/RegEx".
*)

abbreviation str_concat:: "'a word \<Rightarrow> 'a word  \<Rightarrow> 'a word"  where "(str_concat) u v \<equiv> u@v" 
abbreviation str_len:: "'a word \<Rightarrow> int" where  "str_len w \<equiv> of_nat (length w)"
abbreviation str_at:: "'a word \<Rightarrow> int \<Rightarrow> 'a word" where "str_at w i \<equiv> (at w (nat i))"

abbreviation str_substr:: "'a word \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 'a word"  where "str_substr w i n \<equiv> if (n < 0 \<or> i<0 \<or> ((nat i) \<ge> (length w))) then \<epsilon> else  fac w (nat i) (nat n)"

lemma [simp]: "(n < 0 \<or> i<0 \<or> ((nat i) \<ge> (length w))) \<Longrightarrow> str_substr w i n =  \<epsilon>"
  apply(auto)
  done

lemma [simp]: "\<not>(n < 0 \<or> i<0 \<or> ((nat i) \<ge> (length w))) \<Longrightarrow> str_substr w i n = fac w (nat i) (nat n)"
  apply(auto)
  done

abbreviation str_prefixof:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where "str_prefixof \<equiv> Words.is_prefix"
abbreviation str_suffixof:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where "str_suffixof \<equiv> Words.is_suffix"
abbreviation str_contains:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where "str_contains \<equiv> Words.contains"

abbreviation str_indexof:: "'a word \<Rightarrow> 'a word \<Rightarrow> int \<Rightarrow> int" 
  where "str_indexof h n s \<equiv> if s \<ge> 0 then (case find (drop (nat s) h) n of Some r \<Rightarrow> (int r) | option.None \<Rightarrow> -1) else (-1)"

(* Regular Expression Functions *)

abbreviation str_to_re:: "'a word \<Rightarrow> 'a regex" where "str_to_re w \<equiv> regex.Const w"
abbreviation str_in_re:: "'a word \<Rightarrow> 'a regex \<Rightarrow> bool" where "str_in_re w R \<equiv> contains w R"
abbreviation re_none:: "'a regex" where "re_none \<equiv> regex.None"
abbreviation re_allchar:: "'a regex" where "re_allchar \<equiv> regex.Any"
(* missing:  re_all*)

abbreviation re_concat:: "'a regex \<Rightarrow> 'a regex \<Rightarrow> 'a regex"  where "re_concat r1 r2 \<equiv> Concat r1 r2"
abbreviation re_union:: "'a regex \<Rightarrow> 'a regex \<Rightarrow> 'a regex" where "re_union r1 r2 \<equiv> Union r1 r2"
(* missing: re_inter, re_com, re_diff, re_plus, re_opt, re_range, re_pow, re_loop *)
abbreviation re_star:: "'a regex \<Rightarrow>'a regex" where "re_star r \<equiv> Star r"
abbreviation re_plus:: "'a regex \<Rightarrow> 'a regex" where "re_plus r \<equiv> Plus r"


end