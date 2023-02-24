theory Words      
  imports Main "HOL-Library.Sublist" "HOL-Library.List_Lexorder" HOL.Groups
begin


type_synonym 'a word = "'a list"
no_notation append (infixr "@" 65)
notation append (infixr "\<cdot>" 65)
notation Nil ("\<epsilon>")

(* Basic Operations *)
primrec first:: "'a word \<Rightarrow> 'a word" where
"first \<epsilon> = \<epsilon>"|
"first (a#w) = a#\<epsilon>"

lemma first_is_take_1: "first w = take 1 w"
  apply(induct_tac w)
  by(auto)

lemma singleton_word: "(length w) = 1 \<Longrightarrow> EX a. w = a#\<epsilon>"
  by (simp add: length_Suc_conv)

definition at:: "'a word \<Rightarrow> nat \<Rightarrow> 'a word" where "at w i \<equiv> first (drop i w)"


lemma at_overflow[simp]: "i \<ge> length w \<Longrightarrow> at w i = \<epsilon>" 
  by (simp add: at_def)

primrec concat_all:: "'a word list \<Rightarrow> 'a word"
  where
  "concat_all [] = \<epsilon>" |
  "concat_all (w#ws) = w\<cdot>(concat_all ws)"


(* Subword relations *)

(*definition fac :: "'a word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a word" where "fac w s l = take l (drop s w)"*)

(*definition is_prefix:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where "is_prefix v w = ((take (size v) w) = v)"*)
(*definition is_suffix:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where "is_suffix v w = is_prefix (rev v) (rev w)"*)

abbreviation factor:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where "factor \<equiv> sublist"
fun get_factor:: "'a word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a word" ("_[_;_]") where "get_factor w i j = take (j-i) (drop i w)" 



lemma [simp]:"i \<ge> j \<Longrightarrow> w[i;j] = \<epsilon>" by auto
lemma [simp]:"i\<ge> (length w) \<Longrightarrow> w[i;j] = \<epsilon>" by auto
lemma [simp]: "\<epsilon>[i;j] = \<epsilon>" by auto
lemma [simp]: "w[i;i] = \<epsilon>" by auto
lemma [simp]: "j \<ge> (length w) \<Longrightarrow> w[0;j] = w" by auto



lemma at_is_fac_1: "at w i = get_factor w i (i+1)"
  by (simp add: at_def first_is_take_1)

lemma length_additive: "w = u\<cdot>v \<Longrightarrow> (length w) = (length u) + (length v)" by auto


lemma prefix_not_shorter:"(length w) < (length v) \<Longrightarrow> \<not>(prefix v w)"
  by (auto simp add: prefix_def)
 

lemma suffix_not_shorter:"(length w) < (length v) \<Longrightarrow> \<not>(suffix v w)"
  by (auto simp add: suffix_def)
  


lemma factor_embedding:"w[i;j] = v \<Longrightarrow> EX x y. x\<cdot>v\<cdot>y = w"
  apply(auto simp add: get_factor.elims)
  by (metis append_take_drop_id)


lemma strict_factor_embedding:"i<j \<and> i < (length w) \<Longrightarrow> ((w[i;j] = v) \<Longrightarrow> EX x y. x\<cdot>v\<cdot>y = w \<and> (length x) = i \<and> (length v) = min (j-i) ((length w)-i))"
  apply(auto) 
  by (metis append_take_drop_id length_take min.absorb4 min.commute)
  
  


lemma factorization: "w = x\<cdot>u\<cdot>y \<Longrightarrow> u = (w[(length x);(length u)+(length x)])"
proof -
  assume a:"w = x\<cdot>u\<cdot>y"
  then have "w[(length x);(length u)+(length x)] = take (((length u)+(length x)-(length x))) (drop (length x) w)" by simp
  also have "... = take (length u) (drop (length x) w)" by simp
  finally show ?thesis using a by auto
qed

lemma factor_if:"w = x\<cdot>u\<cdot>y \<Longrightarrow> EX i j. (w[i;j]) = u"
  by (metis factorization)
  

lemma factor_size_bound:"w = x\<cdot>v\<cdot>y \<Longrightarrow> (length v) \<le> (length w)"
  by auto


lemma drop_append:"n \<le> (length w) \<and> x = drop n w  \<Longrightarrow> EX v. ((w = v\<cdot>x) \<and> (length v) = n)"
  apply(induct w)
   apply auto
  by (metis append_take_drop_id le_Suc_eq length_Cons length_take min_def not_less_eq_eq)
    


primrec contains:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where
"contains \<epsilon> v = (v = \<epsilon>)" |
"contains (x#u) v = ((prefix v (x#u)) \<or> (contains u v))" 

lemma contains_iff_fac: "contains w v \<longleftrightarrow> factor v w"
  unfolding sublist_def
  apply(induct w)
    apply(auto simp add: prefix_def)+
   apply (metis append_Cons)
  by (metis append_eq_Cons_conv)

lemma not_contains_no_fac_has_prefix:"(\<not>contains w d) \<Longrightarrow> w = x\<cdot>y \<Longrightarrow> (\<not> prefix d y)"
  by (auto simp add: contains_iff_fac sublist_append)
  
lemma if_contains_then_fac_has_prefix:"(contains w d) \<Longrightarrow> EX x y. w = x\<cdot>y \<and> (prefix d y)"
  by (auto simp add: contains_iff_fac prefix_def sublist_def)


lemma epsilon_contains_epsilon[simp]: "contains \<epsilon> v \<Longrightarrow> v = \<epsilon>" by auto


(* Find occurrence of a sub string *)

(* Finds the suffix of a word that starts with a given word *)
definition find_fac:: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word option" where
"find_fac w v = List.find (prefix v) (rev (suffixes w))"

lemma rev_suffixes:"set (suffixes w) = set (rev (suffixes w))"  by auto

lemma suffixes_set:"x \<in> set (suffixes w) \<Longrightarrow> suffix x w"
  by (auto simp add: suffix_def)
  

lemma suffixes_rev_set:"x \<in> set (rev (suffixes w)) \<Longrightarrow> suffix x w"
  by (auto simp add: suffix_def)
  

lemma first_suffix_is_word:"rev (suffixes w)!0 = w"
  by (metis Nil_is_rev_conv hd_conv_nth hd_rev last_suffixes suffixes_not_Nil)

lemma find_prefix: "find_fac (v\<cdot>w) v = Some (v\<cdot>w)"
  apply(auto simp add: find_fac_def)
  by (auto simp add: find_Some_iff first_suffix_is_word prefix_def)
 

lemma find_fac_epsilon: "find_fac w \<epsilon> = Some w"
  unfolding  prefix_def
  by (metis append_Nil find_prefix)
  
lemma find_fac_in_epsilon: "find_fac \<epsilon> w = Some v \<Longrightarrow> w = \<epsilon>"
  by (auto simp add: find_fac_def split: if_splits)
  

lemma find_returns_factor_at:"find_fac w v = Some s \<Longrightarrow> EX x y. w = x\<cdot>v\<cdot>y \<and> (length x) = (length w)-(length s)"
  apply(auto simp add: prefix_def suffix_def find_fac_def)
  by (metis add_diff_cancel_right' find_Some_iff length_append nth_mem prefix_def suffix_def suffixes_rev_set)


lemma contains_iff_find_fac: "(EX u. find_fac w v = Some u) \<longleftrightarrow> contains w v"
  apply(auto)
  using contains_iff_fac find_returns_factor_at apply blast
  apply(auto simp add: contains_iff_fac)
  by (metis find_None_iff2 find_fac_def in_set_suffixes not_Some_eq rev_suffixes sublist_altdef')


lemma suffixes_count: "length (suffixes w) = (length w)+1"
  apply(induct_tac w) by(auto)

lemma suffixes_rev_count[simp]: "length (rev (suffixes w)) = (length (suffixes w))"
  by auto

lemma suffix_length: "i < length (suffixes w) \<Longrightarrow> length ((suffixes w)!i) = i"
  apply(auto)
  apply(induct w)
  by(auto simp add: nth_append)

value "length ((rev (suffixes ''abc''))!1)"

lemma suffix_rev_length: "i < length (rev (suffixes w)) \<Longrightarrow> length ((rev (suffixes w))!i) = (length w) - i"
  apply(auto)
  apply(induct w)
  by (auto simp add: suffix_length  less_Suc_eq_0_disj  rev_nth, auto simp add: suffix_length)

lemma suffix_if:"v = rev ((suffixes w))!j \<and> j < length (rev ((suffixes w))) \<longleftrightarrow> (\<exists>x. w = x\<cdot>v \<and> (length x) = j)"
  apply(auto)
  apply (metis add_diff_cancel_right' add_diff_inverse_nat length_additive length_rev length_suffixes not_less_eq nth_mem suffix_def suffix_rev_length suffixes_rev_set)
  by (simp add: first_suffix_is_word nth_append suffixes_append)


lemma find_fac_returns_first: "find_fac w v = Some s \<Longrightarrow> EX x y. w = x\<cdot>v\<cdot>y \<and> (length x) = (length w) - (length s) \<and> (\<forall> x'. (length x')<(length x) \<longrightarrow> (\<nexists>y'. w = x'\<cdot>v\<cdot>y'))" 
  apply(auto simp add:  find_fac_def find_Some_iff prefix_def)
  by (metis add_diff_cancel_right' length_append length_rev length_suffixes suffix_if)



definition find_index:: "'a word \<Rightarrow> 'a word \<Rightarrow> nat option" where
"find_index w v = (case find_fac w v of Some r \<Rightarrow>  Some ((length w) - (length r)) | None \<Rightarrow> None)"



lemma find_finds_factor:"find_index w v = Some r \<Longrightarrow> EX x y. w = x\<cdot>v\<cdot>y \<and> (length x) = r"
  unfolding find_index_def
  apply(auto simp add: length_additive option.case_eq_if split: if_splits)
  using find_returns_factor_at by blast


lemma contains_iff_find_index: "(EX r. find_index w v = Some r) \<longleftrightarrow> contains w v"
  apply(auto simp add: find_index_def)
  using contains_iff_find_fac by force+


lemma find_index_of_suffix: "find_index (drop i w) v = Some r \<and> i \<le> (length w) \<Longrightarrow> \<exists>x y. w = x\<cdot>v\<cdot>y \<and>  (length x) = r+i"
proof -
  assume a:"find_index (drop i w) v  = Some r \<and> i \<le> (length w)"
  then have "EX s. find_fac (drop  i w) v = Some s"   by (metis find_index_def option.collapse option.distinct(1) option.simps(4)) 
  then have "EX s. find_fac (drop i w) v = Some s \<and> r = (length (drop i w)) - (length s)"   by (metis a find_index_def option.case(2) option.inject)
  then have "EX s x y. (drop  i w) = x\<cdot>v\<cdot>y \<and> (length x) = (length (drop  i w))-(length s) \<and>  r = (length (drop  i w)) - (length s)"  by (metis Ex_list_of_length find_returns_factor_at)
  then have "EX s x y. (drop  i w) = x\<cdot>v\<cdot>y \<and> (length x) = r \<and> r = (length (drop  i w)) - (length s)"  by auto
  then have "EX s x y. (drop  i w) = x\<cdot>v\<cdot>y \<and> i \<le> (length w) \<and> (length x) = r \<and> r = (length (drop  i w)) - (length s)" using a  by auto
  then have "EX s x y. (\<exists>x'. w = x'\<cdot>x\<cdot>v\<cdot>y \<and> (length x') = i) \<and> (length x) = r  \<and> r = (length (drop  i w)) - (length s)"  by (metis Words.drop_append)
  then have "EX s x y x'. w = x'\<cdot>x\<cdot>v\<cdot>y \<and> (length x') = i \<and> (length x) = r  \<and> r = (length (drop  i w)) - (length s)" by auto
  then have "EX x y x'. w = x'\<cdot>x\<cdot>v\<cdot>y \<and> (length x') = i \<and> (length x) = r" by auto
  then have "EX x y. w = x\<cdot>v\<cdot>y \<and> (length x) = r + i"  by (metis append.assoc length_additive add.commute)
  then show ?thesis   by (simp)
qed


lemma find_index_returns_first: "find_index w v = Some s \<Longrightarrow> EX x y. w = x\<cdot>v\<cdot>y \<and> (length x) = s \<and> (\<forall>x'. (length x') < s \<longrightarrow> (\<nexists>y'. w = x'\<cdot>v\<cdot>y'))" 
  unfolding find_index_def
  apply(auto simp add: option.case_eq_if split: if_splits)
  using find_fac_returns_first by metis
  

theorem find_prefix_is_word: "find_fac (v\<cdot>u) v = Some (v\<cdot>u)"
  by (auto simp add:  find_fac_def  prefix_def find_Some_iff first_suffix_is_word)

theorem find_prefix_index_is_0: "find_index (v\<cdot>u) v = Some 0"
  unfolding find_index_def
  using find_prefix_is_word by (metis diff_self_eq_0 option.simps(5))



lemma find_index_of_suffix_returns_first: "i \<le> (length w) \<and> find_index (drop i w) v = Some s \<Longrightarrow> EX x y. w = x\<cdot>v\<cdot>y \<and> (length x) = (s+i) \<and> (\<forall>x'. ((length x') < (s+i) \<and> (length x') \<ge> i) \<longrightarrow> (\<nexists>y'. w = x'\<cdot>v\<cdot>y'))" 
proof -
  assume a:"i \<le> (length w) \<and> find_index (drop i w) v = Some s"
  then have "\<exists>p u. w = p\<cdot>u \<and> length p = i \<and> find_index u v = Some s" using drop_append by fastforce
  then have "\<exists>p u. w = p\<cdot>u \<and> length p = i \<and> (EX x y. u = x\<cdot>v\<cdot>y \<and> (length x) = s \<and> (\<forall>x'. (length x') < s \<longrightarrow> (\<nexists>y'. u = x'\<cdot>v\<cdot>y')))" using find_index_returns_first by metis
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> u = x\<cdot>v\<cdot>y \<and> (length x) = s \<and> (\<forall>x'. (length x') < s \<longrightarrow> (\<nexists>y'. u = x'\<cdot>v\<cdot>y'))" by auto
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = (length p)+s \<and> (\<forall>x'. (length x') < s \<longrightarrow> (\<nexists>y'. u = x'\<cdot>v\<cdot>y'))" by auto
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = i+s \<and> (\<forall>x'. (length x') < s \<and> (length x') \<ge> 0 \<longrightarrow> (\<nexists>y'. u = x'\<cdot>v\<cdot>y'))" by auto
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = i+s \<and> (\<forall>x'. (length x') < s \<and> (length x') \<ge> 0 \<longrightarrow> (\<nexists>y'. p\<cdot>u = p\<cdot>x'\<cdot>v\<cdot>y'))" by blast
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = i+s \<and> (\<forall>x'. (\<nexists>y'.  (length x') < s \<and> (length x') \<ge> 0 \<and>  p\<cdot>u = p\<cdot>x'\<cdot>v\<cdot>y'))" by auto
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = i+s \<and> (\<forall>x' p'. (\<nexists>y'.  (length p') = (length p) \<and> (length x') < s \<and> (length x') \<ge> 0 \<and>  w = p'\<cdot>x'\<cdot>v\<cdot>y'))" by (metis (no_types, opaque_lifting) append_eq_append_conv)
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = i+s \<and> (\<forall>x' p'. (\<nexists>y' x''.  (length p') = (length p) \<and> x''=p'\<cdot>x' \<and> (length x') < s \<and> (length x') \<ge> 0 \<and>  w = x''\<cdot>v\<cdot>y'))" by auto
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = i+s \<and> (\<forall>x' p'. (\<nexists>y' x''.  (length p') = (length p) \<and> x''=p'\<cdot>x' \<and> (length x'') < s+i \<and> (length x'') \<ge> i \<and>  w = x''\<cdot>v\<cdot>y'))" by force
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = i+s \<and> (\<forall>x'. (\<nexists>y' x''.  (length x'') < s+i \<and> (length x'') \<ge> i \<and>  w = x''\<cdot>v\<cdot>y'))"  by (metis Words.drop_append)
  then have "\<exists>x y p u. w = p\<cdot>u \<and> length p = i \<and> p\<cdot>u = p\<cdot>x\<cdot>v\<cdot>y \<and> (length (p\<cdot>x)) = i+s \<and> (\<forall>x''. (\<nexists>y'.  (length x'') < s+i \<and> (length x'') \<ge> i \<and>  w = x''\<cdot>v\<cdot>y'))"  by force
  then have "\<exists>x y.  w = x\<cdot>v\<cdot>y \<and> (length x) = i+s \<and> (\<forall>x''. (\<nexists>y'.  (length x'') < s+i \<and> (length x'') \<ge> i \<and>  w = x''\<cdot>v\<cdot>y'))"  by (metis append.assoc)
  then have "\<exists>x y.  w = x\<cdot>v\<cdot>y \<and> (length x) = s+i \<and> (\<forall>x'. (length x') < s+i \<and> (length x') \<ge> i \<longrightarrow>(\<nexists>y'.   w = x'\<cdot>v\<cdot>y'))"  by (metis add.commute)
  then show ?thesis  .
qed

primrec add_option:: "nat option \<Rightarrow> nat \<Rightarrow> nat option" where
"add_option None _ = None"|
"add_option (Some x) y = Some (x + y)"

lemma add_option_is_0:"add_option x y = (Some 0) \<Longrightarrow> x = (Some 0) \<and> y = 0"  
  apply(auto)
   apply (metis add_option.simps(1) add_option.simps(2) option.collapse option.sel zero_eq_add_iff_both_eq_0)
  by (metis (full_types) add_option.simps(1) add_option.simps(2) option.collapse option.sel zero_eq_add_iff_both_eq_0)


definition replace::"'a word \<Rightarrow> 'a word \<Rightarrow> 'a word \<Rightarrow> 'a word" where
"replace w v u = (case find_index w v of Some i \<Rightarrow> (take i w)\<cdot>u\<cdot>(drop (i+(length v)) w) | None => w)"

lemma replace_epsilon: "replace w \<epsilon> u = u\<cdot>w"
  unfolding replace_def
  apply(auto simp add: option.case_eq_if)
   apply (simp add: find_fac_epsilon find_index_def)
  by (metis append_Nil drop0 find_prefix_index_is_0 option.sel take_eq_Nil2)

lemma replace_id_if_not_contains:"\<not>contains w v \<Longrightarrow> replace w v u = w"
  unfolding replace_def
  using contains_iff_find_index  by fastforce


theorem replace_factor: "contains w v \<Longrightarrow> \<exists>x y. (w= x\<cdot>v\<cdot>y \<and> replace w v u = x\<cdot>u\<cdot>y)"
  unfolding replace_def find_index_def
  apply(auto simp add: option.case_eq_if prefix_def )
  apply (metis contains_iff_find_fac option.distinct(1))
  by (metis append.assoc append_eq_conv_conj find_returns_factor_at length_additive)
  
  

theorem replace_first_factor: "contains w v \<Longrightarrow> \<exists>x y. replace w v u = x\<cdot>u\<cdot>y \<and> w = x\<cdot>v\<cdot>y \<and> (\<forall> x'. (length x') < (length x) \<longrightarrow> (\<nexists>y'. w=x'\<cdot>v\<cdot>y'))"
  apply(auto simp add: contains_iff_find_index)
  unfolding replace_def
  apply(auto simp add: option.case_eq_if contains_iff_find_index)
   apply (metis contains_iff_find_index option.distinct(1))
  proof -
    assume a: "contains w v"
    obtain aas :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" and aasa :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
      f2: "\<forall>as asa n. length (aas n asa as) = n \<and> aas n asa as \<cdot> asa \<cdot> aasa n asa as = as \<or> find_index as asa \<noteq> Some n"
      by (metis (no_types) find_finds_factor)
    obtain nn :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat" where
      f3: "find_index w v = Some (nn v w)"
      using a by (meson contains_iff_find_index)
    then have "drop (nn v w + length v) w = aasa (nn v w) v w"
      using f2 by (metis append.assoc append_eq_conv_conj length_additive)
    then show "\<exists>as asa. take (the (find_index w v)) w \<cdot> u \<cdot> drop (the (find_index w v) + length v) w = as \<cdot> u \<cdot> asa \<and> w = as \<cdot> v \<cdot> asa \<and> (\<forall>asa. length asa < length as \<longrightarrow> (\<forall>as. w \<noteq> asa \<cdot> v \<cdot> as))"
      using f3 f2 by (metis append_eq_conv_conj find_index_returns_first option.sel)
  qed
  
 
end





