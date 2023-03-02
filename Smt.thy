theory Smt
  imports Main
begin

no_notation Groups.abs_class.abs  ("\<bar>_\<bar>")


(* 
The standard explicitly states lexicographic order but this cannot be enforced here.
Replace_all, replace_re, and replace_all_re are still missing.
*)

locale strings = 
  monoid  str_concat empty +
  order_str: linorder str_less_eq str_less 
 
  for 
      str_concat:: "'str \<Rightarrow> 'str \<Rightarrow> 'str" (infixr "\<cdot>" 100) and
      empty:: "'str"  ("\<epsilon>") and
      str_less_eq:: "'str \<Rightarrow> 'str \<Rightarrow> bool"  (infix "\<le>" 50) and 
      str_less::"'str \<Rightarrow> 'str \<Rightarrow> bool" (infix "<" 50)
      and int_leq::"int \<Rightarrow> int \<Rightarrow> bool" 
      and int_le::"int \<Rightarrow> int \<Rightarrow> bool" +
fixes 
    str_len:: "'str \<Rightarrow> int" ("\<bar>_\<bar>") and
    str_at:: "'str \<Rightarrow> int \<Rightarrow> 'str" and
    str_substr:: "'str \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 'str" and
    str_prefixof:: "'str \<Rightarrow> 'str \<Rightarrow> bool" (infix "\<sqsubseteq>" 65) and
    str_suffixof:: "'str \<Rightarrow> 'str \<Rightarrow> bool" (infix "\<sqsupseteq>" 65) and
    str_contains:: "'str \<Rightarrow> 'str \<Rightarrow> bool" and
    str_indexof:: "'str \<Rightarrow> 'str \<Rightarrow> int \<Rightarrow> int"  and    
    str_replace:: "'str \<Rightarrow> 'str \<Rightarrow> 'str \<Rightarrow> 'str" and
    str_in_re:: "'str \<Rightarrow> 're \<Rightarrow> bool"  and
    str_to_re:: "'str \<Rightarrow> 're" and
    re_none:: "'re" and
    re_allchar:: "'re" and
    re_concat:: "'re \<Rightarrow> 're \<Rightarrow> 're" and
    re_union:: "'re \<Rightarrow> 're \<Rightarrow> 're" and
    re_inter:: "'re \<Rightarrow> 're \<Rightarrow> 're" and
    re_star:: "'re \<Rightarrow>'re" and
    re_plus:: "'re \<Rightarrow> 're" and
    re_range:: "'str \<Rightarrow> 'str \<Rightarrow> 're" and
    re_opt::"'re \<Rightarrow> 're" and
    re_comp::"'re \<Rightarrow> 're" and
    re_diff:: "'re \<Rightarrow> 're \<Rightarrow> 're" and
    re_pow::"nat \<Rightarrow> 're \<Rightarrow> 're" and
    re_loop:: "nat \<Rightarrow> nat \<Rightarrow> 're \<Rightarrow> 're" and

    lang:: "'re \<Rightarrow> 'str set"
  assumes
concat_assoc: "u\<cdot>(v\<cdot>w) = (u\<cdot>v)\<cdot>w" and
concat_lneutral: "a\<cdot>\<epsilon> = a" and
concat_rneutral: "\<epsilon>\<cdot>a = a" and

len_epsi: "\<bar>w\<bar> = 0 \<longleftrightarrow> w = \<epsilon>" and
len_monotonicity: "\<bar>a\<cdot>b\<bar> = \<bar>a\<bar> + \<bar>b\<bar>" and    

str_at: "str_at w n = str_substr w n 1" and

str_substr1: "0 \<le> m \<and> m < \<bar>w\<bar> \<and> 0 < n \<Longrightarrow> \<exists>!v. str_substr w m n = v \<and> (\<exists>x y. w =  x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = m \<and>  \<bar>v\<bar> = min n (\<bar>w\<bar> - m))" and
str_substr2: "\<not>(0 \<le> m \<and> m <  \<bar>w\<bar> \<and> 0 < n) \<Longrightarrow> str_substr w m n = \<epsilon>" and

str_prefix: "v\<sqsubseteq>w \<longleftrightarrow> (\<exists>x. w = v\<cdot>x)" and
str_suffix: "v\<sqsupseteq>w \<longleftrightarrow> (\<exists>x. w = x\<cdot>v)" and
str_contains: "str_contains w v \<longleftrightarrow> (\<exists>x y. w = x\<cdot>v\<cdot>y)" and

(* This is stated in SMT-LIB but invalid
str_indexof1: "str_contains v w \<Longrightarrow> \<exists>n. str_indexof w v i = n \<and> (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> i \<le> n \<and> n = \<bar>x\<bar>) \<and> (\<forall>n'. n' < n \<longrightarrow> (\<exists>x' y'. w = x'\<cdot>v\<cdot>y' \<and> i \<le> n' \<and> n = \<bar>x'\<bar>))" and
str_indexof2: "\<not> str_contains v w \<Longrightarrow> str_indexof w v i = -1" and
*)

str_indexof1: "i\<ge>0 \<and> str_contains (str_substr w i \<bar>w\<bar>) v \<Longrightarrow> \<exists>n. str_indexof w v i = n \<and> (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> i \<le> n \<and> n = \<bar>x\<bar>) \<and> (\<forall>n'. n' < n \<longrightarrow> (\<exists>x' y'. w = x'\<cdot>v\<cdot>y' \<and> i \<le> n' \<and> n = \<bar>x'\<bar>))" and
str_indexof2: "i<0 \<or> \<not> str_contains (str_substr w i \<bar>w\<bar>) v \<Longrightarrow> str_indexof w v i = -1" and 


replace1: "str_contains w v \<Longrightarrow> \<exists>x y. str_replace w v u = x\<cdot>u\<cdot>y \<and> w = x\<cdot>v\<cdot>y \<and> (\<forall> x'. \<bar>x'\<bar> < \<bar>x\<bar> \<longrightarrow> (\<nexists>y'. w=x'\<cdot>v\<cdot>y'))" and
replace2: "\<not> str_contains w v \<Longrightarrow> str_replace w v u = w" and


in_re:"str_in_re w R \<longleftrightarrow> w \<in> (lang R)"  and
to_re: "lang (str_to_re w) = {w}" and
re_none: "lang re_none = {}" and
re_allchar: "lang re_allchar = {w. \<bar>w\<bar> = 1}" and
re_concat: "lang (re_concat r e) = {x\<cdot>y|x y. x \<in> lang r \<and> y \<in> lang e}" and
re_union: "lang (re_union r e) = {w|w. w \<in> lang r \<or> w \<in> lang e}" and
re_inter: "lang (re_inter r1 r2) = {w|w. w\<in> lang r1 \<and> w \<in> lang r2}" and

re_star: "lang (re_star r) = k \<Longrightarrow> empty \<in> k \<and> {x\<cdot>y|x y. x \<in> lang r \<and> y \<in> k} \<subseteq> k" and

re_plus: "lang (re_plus r) = lang (re_concat r (re_star r))" and
re_range1: "\<bar>l\<bar> = 1 \<and> \<bar>u\<bar> = 1 \<Longrightarrow> lang (re_range l u) = {v| v. l \<le> v \<and>  v\<le>u \<and> \<bar>v\<bar> = 1}" and
re_range2: "\<bar>l\<bar> \<noteq> 1 \<or> \<bar>u\<bar> \<noteq> 1 \<Longrightarrow> lang (re_range l u) = {}" and
re_comp: "lang (re_comp r) = UNIV - (lang r)" and
re_diff: "lang (re_diff r1 r2) = lang r1 - lang r2" and
re_pow1: "lang (re_pow 0 r) = {\<epsilon>}" and
re_pow2: "\<forall>n. re_pow (Suc n) r =  re_concat r (re_pow n r)" and
re_loop1: "\<And> a b. a \<le> b \<Longrightarrow> lang (re_loop a b r) = (\<Union>x\<in>{a..b}. lang (re_pow x r))" and
re_loop2: "\<And> a b. a > b \<Longrightarrow> lang (re_loop a b r) = {}"

end