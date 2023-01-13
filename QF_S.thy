theory QF_S
  imports RegEx Words
begin

(* Core functions *)

(* str.++ *)
abbreviation str_concat:: "'a word \<Rightarrow> 'a word  \<Rightarrow> 'a word"  where "(str_concat) u v \<equiv> u*v" 
(* str.len *)
abbreviation str_len:: "'a word \<Rightarrow> nat" where  "str_len w \<equiv> size w"

(* Regular Expression Functions *)

abbreviation str_to_re:: "'a word \<Rightarrow> 'a regex" where "str_to_re w \<equiv> RegEx.Const w"
abbreviation str_in_re:: "'a word \<Rightarrow> 'a regex \<Rightarrow> bool" where "str_in_re w R \<equiv> contains w R"
abbreviation re_none:: "'a regex" where "re_none \<equiv> None"
(* missing:  re_all, re_allchar *)

(* re.++ *)
abbreviation re_concat:: "'a regex \<Rightarrow> 'a regex \<Rightarrow> 'a regex"  where "re_concat r1 r2 \<equiv> Concat r1 r2"
abbreviation re_union:: "'a regex \<Rightarrow> 'a regex \<Rightarrow> 'a regex" where "re_union r1 r2 \<equiv> Union r1 r2"
(* missing: re_inter, re_com, re_diff, re_plus, re_opt, re_range, re_pow, re_loop *)
abbreviation re_star:: "'a regex \<Rightarrow>'a regex" where "re_star r \<equiv> Star r"


end