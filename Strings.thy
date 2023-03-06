theory Strings
  imports Core "strings/RegEx" "strings/Words"  "HOL-Library.Numeral_Type" Smt
begin

no_notation List.length ("\<bar>_\<bar>")
no_notation Groups.abs_class.abs  ("\<bar>_\<bar>")


section "An interpretation for the theory of string"


subsection "Definition of Unicode characters"

type_synonym uc_word = "196607 word"

type_synonym uc_regex = "196607 regex"

definition UC:: "uc_word set" where "UC = {w. True}"

lemma "UNIV = UC"  
  by (simp add: UC_def)


subsection "Implementation of string constraints"

abbreviation str_concat:: "uc_word \<Rightarrow> uc_word  \<Rightarrow> uc_word" where 
  "(str_concat) u v \<equiv> u\<cdot>v" 

abbreviation str_len:: "uc_word \<Rightarrow> int" ("\<bar>_\<bar>") where  
  "str_len w \<equiv> of_nat (length w)"

abbreviation str_at:: "uc_word \<Rightarrow> int \<Rightarrow> uc_word" where 
  "str_at w i \<equiv> if i \<ge> 0 then w[(nat i); (nat i+1)] else \<epsilon>"

abbreviation str_substr:: "uc_word \<Rightarrow> int \<Rightarrow> int \<Rightarrow> uc_word" where 
  "str_substr w m n \<equiv> if (n \<ge> 0 \<and> 0\<le>m \<and> ((nat m) \<le> (length w)-1)) then  w[(nat m);(nat (m+n))] else \<epsilon>"

abbreviation str_prefixof:: "uc_word \<Rightarrow> uc_word \<Rightarrow> bool" where 
  "str_prefixof \<equiv> prefix"

abbreviation str_suffixof:: "uc_word \<Rightarrow> uc_word \<Rightarrow> bool" where 
  "str_suffixof \<equiv> suffix"

abbreviation str_contains:: "uc_word \<Rightarrow> uc_word \<Rightarrow> bool" where 
  "str_contains \<equiv> Words.contains"

abbreviation str_indexof:: "uc_word \<Rightarrow> uc_word \<Rightarrow> int \<Rightarrow> int" where 
  "str_indexof h n s \<equiv> 
     if s \<ge> 0 then 
       (case find_index (drop (nat s) h) n of 
           Some r \<Rightarrow> (int r+s) 
         | option.None \<Rightarrow> -1
       ) 
     else (-1)"

abbreviation str_replace:: "uc_word \<Rightarrow> uc_word \<Rightarrow> uc_word \<Rightarrow> uc_word" where 
  "str_replace \<equiv> replace"

abbreviation str_in_re:: "uc_word \<Rightarrow> uc_regex \<Rightarrow> bool" where 
  "str_in_re w R \<equiv> re_contains w R"

abbreviation str_to_re:: "uc_word \<Rightarrow> uc_regex" where 
  "str_to_re w \<equiv> regex.Const w"

abbreviation re_none:: "uc_regex" where 
  "re_none \<equiv> regex.None"

abbreviation re_allchar:: "uc_regex" where 
  "re_allchar \<equiv> regex.Any"

abbreviation re_concat:: "uc_regex \<Rightarrow> uc_regex \<Rightarrow> uc_regex" where 
  "re_concat \<equiv> RegEx.re_concat"

abbreviation re_union:: "uc_regex \<Rightarrow> uc_regex \<Rightarrow> uc_regex" where
  "re_union  \<equiv> RegEx.re_union"

abbreviation re_inter:: "uc_regex \<Rightarrow> uc_regex \<Rightarrow> uc_regex" where 
  "re_inter  \<equiv> RegEx.re_inter"

abbreviation re_star:: "uc_regex \<Rightarrow>uc_regex" where 
  "re_star \<equiv> RegEx.re_star"

abbreviation re_plus:: "uc_regex \<Rightarrow> uc_regex" where 
  "re_plus r \<equiv> RegEx.re_plus r"

fun re_range:: "uc_word \<Rightarrow> uc_word \<Rightarrow> uc_regex" where 
  "re_range (l#\<epsilon>) (u#\<epsilon>) = RegEx.re_range l u"|
  "re_range _ _ = RegEx.None"

abbreviation re_opt::"uc_regex \<Rightarrow> uc_regex" where 
  "re_opt r \<equiv> re_union (Const \<epsilon>) r"

abbreviation re_comp::"uc_regex \<Rightarrow> uc_regex" where
  "re_comp \<equiv> RegEx.re_comp"

abbreviation re_diff:: "uc_regex \<Rightarrow> uc_regex \<Rightarrow> uc_regex" where
  "re_diff \<equiv> RegEx.re_diff"

abbreviation re_pow::"nat \<Rightarrow> uc_regex \<Rightarrow> uc_regex" where
  "re_pow n r \<equiv> RegEx.re_pow r n"

abbreviation re_loop:: "nat \<Rightarrow> nat \<Rightarrow> uc_regex \<Rightarrow> uc_regex" where 
  "re_loop a b r \<equiv> RegEx.re_loop r a b"


section "String Length"

lemma length_ge_0: "\<bar>w\<bar> \<ge> 0" 
  by auto

lemma length_less_0: "\<not>\<bar>w\<bar> < 0" 
  by auto

lemma length_int_nat: "\<bar>w\<bar> = int (length w)" 
  by auto

lemma length_int_nat_le: "m \<ge> 0 \<Longrightarrow> m \<le> \<bar>w\<bar> \<longleftrightarrow> (nat m) \<le> (length w)"
  by auto

lemma length_int_nat_sub: "m \<ge> 0 \<Longrightarrow> m \<le> \<bar>w\<bar> \<Longrightarrow> int ((length w) - (nat m)) = (\<bar>w\<bar> - m)"
  by auto

lemma length_int_nat_min: "m \<ge> 0 \<Longrightarrow> n \<ge> 0 \<Longrightarrow> int (min (nat m) (nat n)) = min m n"
  by auto

lemma length_int_nat_sub_min:
  assumes "\<bar>w\<bar> \<ge> m"
    and "n \<ge> 0"
    and "m \<ge> 0"
  shows "int (min (nat n) ((length w)-nat m)) = (min n (\<bar>w\<bar>- m))"
  using assms by auto

lemma of_nat_nat_inv: "x \<ge> 0 \<Longrightarrow> of_nat (nat x) = x" 
  by auto


section "Substring, Prefix, Suffix, Indexof"


subsection "Substrings"

lemma substr_factor_equal:
  assumes "0 \<le> m"
    and "m < \<bar>w\<bar>"
    and "0 < n"
  shows "str_substr w m n = (w[nat m; nat m + nat n])"
  using assms diff_nat_eq_if by auto

theorem substr_correct1: 
  fixes m::"int" and n::"int"
  assumes "0 \<le> m"
    and "m < \<bar>w\<bar>"
    and "0 < n" 
  shows "\<exists>!v. str_substr w m n = v \<and> (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = m \<and> \<bar>v\<bar> = (min n (\<bar>w\<bar> - m) ))"
proof -
  from assms have "nat m < (length w) \<and> nat m \<le> nat m + nat n" by auto
  then have "\<exists>!v. (w[nat m; nat m + nat n]) = v \<and>
             (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> (length x) = nat m \<and>
               (length v) = min ((nat m + nat n)-nat m) ((length w)-nat m))" 
    using factorization by metis
  then have "\<exists>!v. (w[nat m; nat m + nat n]) = v \<and>
             (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = m \<and> (length v) = min (nat n) ((length w)-nat m))" 
    by (metis add_diff_cancel_left' assms(1) int_nat_eq)
  then have "\<exists>!v. str_substr w m n = v \<and>
             (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = m \<and> (length v) = min (nat n) ((length w)-nat m))" 
    using assms substr_factor_equal by presburger
  then have "\<exists>!v. str_substr w m n = v \<and>
             (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = m \<and> \<bar>v\<bar> = int (min (nat n) ((length w)-nat m)))" 
    by simp
  then have "\<exists>!v. str_substr w m n = v \<and> (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = m \<and> \<bar>v\<bar> = (min n (\<bar>w\<bar>- m)))" 
    using length_int_nat_sub_min assms by auto
  then show ?thesis 
    by blast
qed

theorem substr_correct2:
  shows "\<not>(0\<le>m \<and> m < \<bar>w\<bar> \<and> 0 < n) \<Longrightarrow> (str_substr w m n = \<epsilon>)"
  by auto


subsection "Prefix"

(* Correctness of prefixof: \<lbrakk>str.prefixof\<rbrakk>(v, w) = true iff w = vx₂ for some word x *)
theorem prefixof_correct: "str_prefixof v w \<longleftrightarrow> (EX x. w = v@x)"
  by (simp add: prefix_def)


subsection "Suffix"

(* Correctness of suffixof: \<lbrakk>str.suffixof\<rbrakk>(v, w) = true iff w = xv₂ for some word x *)
theorem suffix_correct: "str_suffixof v w \<longleftrightarrow> (EX x. w = x@v)"
  by (simp add: suffix_def) 


subsection "Indexof"

theorem indexof_correct1:
  fixes i::int
  assumes "i\<ge>0" and "str_contains (str_substr w i \<bar>w\<bar>) v"
  shows "\<exists>n. str_indexof w v i = n \<and> (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> i \<le> n \<and> n = \<bar>x\<bar>) \<and> (\<forall>n'. n' < n \<longrightarrow> (\<exists>x' y'. w = x'\<cdot>v\<cdot>y' \<and> i \<le> n' \<and> n = \<bar>x'\<bar>))"
  sorry

theorem indexof_correct2: 
  "(i < 0 \<or> \<not>(str_contains (str_substr w i \<bar>w\<bar>) v)) \<Longrightarrow> (str_indexof w v i) = -1"
  sorry


section "Regular Constraints"

theorem re_range_correct1: "(length l) = 1 \<and> (length u) = 1 \<Longrightarrow> (lang (re_range l u)) = {v|v. l \<le> v \<and> v \<le> u \<and> \<bar>v\<bar> = 1}" 
  apply(cases \<open>(l, u)\<close> rule:re_range.cases)
      apply (auto split: if_splits)
   apply (metis (no_types, lifting) Cons_less_Cons length_0_conv length_Suc_conv linorder_not_le)
  by (meson Cons_le_Cons dual_order.trans)

theorem re_range_correct2: "(length l) \<noteq> 1 \<or> (length u) \<noteq> 1 \<Longrightarrow> (lang (re_range l u)) = {}" 
  by (cases \<open>(l, u)\<close> rule:re_range.cases) (auto split: if_splits)


theorem re_pow_correct2: "lang (re_pow (Suc n) r ) = concat (lang r) (lang (re_pow n r))"
  by (simp add: RegEx.re_concat_correct)

theorem re_loop_correct1:
  assumes "a \<le> b"
  shows "lang (re_loop a b r) = (\<Union>x\<in>{a..b}. (lang (re_pow x r)))"
  using re_loop_iff1[of a b] using assms atLeastAtMost_iff by fastforce

(* missing: re_all *)


subsection "Valid interpretation of SMT-LIB theory of Strings"

interpretation uc_strings: Smt.strings
  str_concat \<epsilon> less_eq less less_eq less str_len str_at str_substr str_prefixof str_suffixof 
  str_contains str_indexof str_replace str_in_re str_to_re
  re_none re_allchar re_concat re_union re_inter re_star re_plus re_range re_opt re_comp
  re_diff re_pow re_loop RegEx.lang
proof (unfold_locales)
  fix u v w::uc_word
  fix n m i:: int
  show "u\<cdot>(v\<cdot>w) =  (u\<cdot>v)\<cdot>w" 
    by auto 
  show "w\<cdot>\<epsilon> = w" 
    by auto
  show "\<epsilon>\<cdot>w = w" 
    by auto
  show "\<bar>w\<bar> = 0 \<longleftrightarrow> w = \<epsilon>" 
    by auto 
  show "\<bar>u\<cdot>v\<bar> = \<bar>u\<bar> + \<bar>v\<bar>" 
    by auto
  show "str_at w n = str_substr w n 1" 
    by (simp split: if_splits add: diff_nat_eq_if)
  show str_substr1: 
    "0 \<le> m \<and> m < \<bar>w\<bar> \<and> 0 < n \<Longrightarrow>
        \<exists>!v. str_substr w m n = v \<and> 
        (\<exists>x y. w =  x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = m \<and> \<bar>v\<bar> = min n (\<bar>w\<bar> - m))" 
    using substr_correct1 by auto 
  show str_substr2: "\<not>(0 \<le> m \<and> m < \<bar>w\<bar> \<and> 0 < n) \<Longrightarrow> str_substr w m n = \<epsilon>" 
    using substr_correct2 by presburger
  show "str_prefixof v w \<longleftrightarrow>( \<exists>u. w = v\<cdot>u)" 
    by (simp add: prefix_def)
  show "str_suffixof v w \<longleftrightarrow> (\<exists>u. w = u\<cdot>v)"
    by (simp add: suffix_def)
  show "str_contains w v \<longleftrightarrow> (\<exists>x y. w = x\<cdot>v\<cdot>y)" 
    using contains_iff_factor sublist_def by blast
  show "i\<ge> 0 \<and> str_contains (str_substr w i \<bar>w\<bar>) v \<Longrightarrow> 
          \<exists>n. str_indexof w v i = n \<and> 
            (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> i \<le> n \<and> n = \<bar>x\<bar>) \<and> 
            (\<forall>n'. n' < n \<longrightarrow> (\<exists>x' y'. w = x'\<cdot>v\<cdot>y' \<and> i \<le> n' \<and> n = \<bar>x'\<bar>))" 
    using indexof_correct1 by auto
  show "i<0 \<or> \<not> str_contains (str_substr w i \<bar>w\<bar>) v  \<Longrightarrow> str_indexof w v i = -1" 
    using indexof_correct2 by auto
  show "str_contains w v \<Longrightarrow> 
          \<exists>x y. str_replace w v u = x\<cdot>u\<cdot>y \<and> w = x\<cdot>v\<cdot>y \<and> (\<forall> x'. \<bar>x'\<bar> < \<bar>x\<bar> \<longrightarrow> (\<nexists>y'. w=x'\<cdot>v\<cdot>y'))" 
    using replace_first_factor by fastforce
  show "\<not> str_contains w v \<Longrightarrow> str_replace w v u = w"
    by (simp add: replace_id_if_not_contains)

  fix r e::uc_regex
  fix k::"uc_word set"
  fix a b::"nat"
  show "str_in_re w r \<longleftrightarrow> w \<in> (lang r)" 
    by (auto simp add: re_contains_def derivative_correctness)
  show "lang (str_to_re w) = {w}" 
    by simp
  show "lang re_none = {}" 
    by simp
  show "lang re_allchar = {w. int (length w) = 1}" 
    by simp
  show "lang (re_concat r e) = {str_concat x y |x y. x \<in> lang r \<and> y \<in> lang e}"
    by (simp add: Regular.concat_def re_concat_correct)
  show "lang (Strings.re_union r e) = {w |w. w \<in> lang r \<or> w \<in> lang e}"
    by (simp add: Un_def re_union_correct)
  show "lang (Strings.re_inter r e) = {w |w. w \<in> lang r \<and> w \<in> lang e}"
    by (auto simp add: re_inter_correct)
  show "lang (Strings.re_star r) = k \<Longrightarrow> \<epsilon> \<in> k \<and> {str_concat x y |x y. x \<in> lang r \<and> y \<in> k} \<subseteq> k" 
    using concat_star_subset re_star_correct  Regular.concat_def by fastforce
  show "lang (Strings.re_plus r) = lang (Strings.re_concat r (Strings.re_star r))" 
    by (simp add: re_plus_def)
  show "\<bar>u\<bar> = 1 \<and> \<bar>w\<bar> = 1 \<Longrightarrow> lang (Strings.re_range u w) = {v |v. u \<le> v \<and> v \<le> w \<and> int (length v) = 1}" 
    using re_range_correct1 by simp
  show "\<bar>u\<bar> \<noteq> 1 \<or> \<bar>w\<bar> \<noteq> 1 \<Longrightarrow> lang (Strings.re_range u w) = {}"
    by (simp add: re_range_correct2)
  show "lang (re_comp r) = UNIV - lang r" 
    by (auto simp add: re_comp_correct UC_def)
  show "lang (re_diff r e) = lang r - lang e"
    by (simp add: re_diff_correct)
  show "lang (re_pow 0 r) = {\<epsilon>}" 
    by auto
  show "\<forall>n. Strings.re_pow (Suc n) r = Strings.re_concat r (Strings.re_pow n r)" 
    by simp
  show "a \<le> b \<Longrightarrow> lang (Strings.re_loop a b r) = (\<Union>x\<in>{a..b}. lang (Strings.re_pow x r))" 
    using re_loop_correct1 by presburger
  show "b < a \<Longrightarrow> lang (Strings.re_loop a b r) = {}" 
    by (simp add: re_loop_iff2)
qed

lemmas defs = replace_def find_fac_def find_index_def contains_def re_plus_def suffix_def prefix_def

end