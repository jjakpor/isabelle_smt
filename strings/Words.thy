theory Words      
  imports Main "HOL-Library.Sublist"
begin

no_notation Groups.times_class.times (infixl "*" 70)


type_synonym 'a word = "'a list"
abbreviation Epsilon::"'a word" ("\<epsilon>") where "Epsilon \<equiv> []" 



(* Basic Operations *)


primrec first:: "'a word \<Rightarrow> 'a word" where
"first \<epsilon> = \<epsilon>"|
"first (a#w) = a#\<epsilon>"


lemma singleton_word: "(length w) = 1 \<Longrightarrow> EX a. w = a#\<epsilon>"
  by (simp add: length_Suc_conv)

definition at:: "'a word \<Rightarrow> nat \<Rightarrow> 'a word" where "at w i \<equiv> first (drop i w)"

lemma at_overflow[simp]: "i \<ge> length w \<Longrightarrow> at w i = \<epsilon>" 
  by (simp add: at_def)

primrec concat_all:: "'a word list \<Rightarrow> 'a word"
  where
  "concat_all [] = Epsilon" |
  "concat_all (w#ws) = w@(concat_all ws)"


(* Substring relations *)

definition fac :: "'a word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a word" where "fac w s l = take l (drop s w)"
definition is_prefix:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where "is_prefix v w = ((take (size v) w) = v)"
definition is_suffix:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where "is_suffix v w = is_prefix (rev v) (rev w)"
definition is_not_prefix:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where "is_not_prefix v w = (\<not>is_prefix v w)"


lemma length_additive: "w = u@v \<Longrightarrow> (length w) = (length u) + (length v)" by auto

lemma [simp]:"fac w 0 (size w) = w"
  unfolding fac_def
  apply(auto)
  done

lemma [simp]: "fac Epsilon s l = Epsilon"
  unfolding fac_def
  apply(auto)
  done

lemma [simp]: "length (fac w s 0) = 0"
  apply(auto simp add: fac_def)
  done


lemma prefix_not_shorter[simp]:"(length w) < (length v) \<Longrightarrow> \<not>(is_prefix v w)"
  apply(auto simp add: is_prefix_def)
  done


lemma suffix_not_shorter[simp]:"(length w) < (length v) \<Longrightarrow> \<not>(is_suffix v w)"
  apply(auto simp add: is_suffix_def)
  done


lemma factor_embedding:"fac w s l = u \<Longrightarrow> EX x y. x@u@y = w"
  unfolding fac_def  
  apply (metis append_take_drop_id)
  done

lemma factorization:"w = x@u@y \<Longrightarrow> EX s l. fac w s l = u"
  unfolding fac_def  
  apply (metis append_eq_conv_conj)
  done

lemma factor_size_bound:"w = x@v@y \<Longrightarrow> (length v) \<le> (length w)"
  by auto

fun strip_n:: "nat \<Rightarrow> 'a word \<Rightarrow> 'a word" where
"strip_n 0 w = w"|
"strip_n n \<epsilon> = \<epsilon>"|
"strip_n (Suc n) (a#w) = strip_n n w"




lemma drop_append:"n \<le> (length w) \<and> x = drop n w  \<Longrightarrow> EX v. ((w = v@x) \<and> (length v) = n)"
  apply(induct w)
   apply auto
  by (metis append_take_drop_id le_Suc_eq length_Cons length_take min_def not_less_eq_eq)
  

lemma prefix_iff_startswith: "is_prefix u w \<longleftrightarrow> (EX r. w = u@r)"
  apply(auto simp add: is_prefix_def)
  by (metis append_take_drop_id)

lemma prefix_refl[simp]:"is_prefix w w" by (auto simp add: is_prefix_def)

lemma suffix_iff_endswith: "is_suffix u w \<longleftrightarrow> (EX r. w = r@u)"
  apply(auto simp add: is_prefix_def is_suffix_def)
  by (metis append_take_drop_id rev_append rev_rev_ident)

lemma suffix_refl[simp]:"is_suffix w w" by (auto simp add: is_suffix_def)


primrec contains:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where
"contains \<epsilon> v = (v = \<epsilon>)" |
"contains (x#u) v = ((is_prefix v (x#u)) \<or> (contains u v))" 

lemma contains_iff_fac: "contains w v \<longleftrightarrow> (EX x y. w = x@v@y)"
  apply(induct w)
   apply(auto simp add: prefix_iff_startswith is_prefix_def)+
   apply (metis append_Cons)
  by (metis append_eq_Cons_conv)

lemma not_contains_no_fac_has_prefix:"(\<not>contains w d) \<Longrightarrow> w = x@y \<Longrightarrow> (\<not> is_prefix d y)"
  apply(auto simp add: contains_iff_fac)
  by (metis prefix_iff_startswith)

lemma if_contains_then_fac_has_prefix:"(contains w d) \<Longrightarrow> EX x y. w = x@y \<and> (is_prefix d y)"
  apply(auto simp add: contains_iff_fac)
  using prefix_iff_startswith by blast

lemma epsilon_contains_epsilon: "contains \<epsilon> v \<Longrightarrow> v = \<epsilon>"
  by auto




(* Find occurrence of a sub string *)


(* Finds the suffix of a word that starts with a given word *)
definition find_fac:: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word option" where
"find_fac w v = List.find (is_prefix v) (rev (suffixes w))"

lemma rev_suffixes:"set (suffixes w) = set (rev (suffixes w))"  by auto

lemma suffixes_set:"x \<in> set (suffixes w) \<Longrightarrow> is_suffix x w"
  apply(auto simp add: suffix_iff_endswith)
  using suffix_def by blast

lemma suffixes_rev_set:"x \<in> set (rev (suffixes w)) \<Longrightarrow> is_suffix x w"
  apply(auto simp add: suffix_iff_endswith)
  using suffix_def by blast

lemma first_suffix_is_word:"rev (suffixes w)!0 = w"
  by (metis Nil_is_rev_conv hd_conv_nth hd_rev last_suffixes suffixes_not_Nil)

lemma find_fac_epsilon: "find_fac w \<epsilon> = Some w"
  unfolding find_fac_def is_prefix_def
  apply(auto)
  by (metis find_Some_iff first_suffix_is_word length_rev length_suffixes not_less_zero zero_less_Suc)

lemma find_fac_in_epsilon: "find_fac \<epsilon> w = Some v \<Longrightarrow> w = \<epsilon>"
  apply(auto simp add: find_fac_def)
  using prefix_iff_startswith by fastforce

lemma find_returns_factor_at:"find_fac w v = Some s \<Longrightarrow> EX x y. w = x@v@y \<and> (length x) = (length w)-(length s)"
  apply(auto simp add:Words.find_fac_def)
  by (metis add_diff_cancel_right' find_Some_iff length_append nth_mem prefix_iff_startswith suffix_iff_endswith suffixes_rev_set)

lemma find_returns_first:"find_fac w v = Some s \<Longrightarrow> \<forall> s'. (s' \<in> set (suffixes w) \<and> (length s') > (length s)) \<longrightarrow> \<not> is_prefix s' v"
  apply(auto simp add:Words.find_fac_def)
  by (metis antisym_conv3 find_Some_iff2 nless_le order.strict_trans1 prefix_not_shorter)

lemma contains_iff_find_fac: "(EX u. find_fac w v = Some u) \<longleftrightarrow> contains w v"
  apply(auto)
   apply (metis contains_iff_fac find_returns_factor_at)
  apply(auto simp add: contains_iff_fac)
  by (metis find_None_iff2 find_fac_def in_set_suffixes option.exhaust_sel prefix_iff_startswith set_rev suffix_def)


lemma fac_retains:"find_fac w v = Some r \<Longrightarrow> EX r'. find_fac (u@w) v = Some r'"
  apply(auto simp add: find_fac_def)
  by (metis append.assoc contains_iff_fac contains_iff_find_fac find_fac_def)




definition find_index:: "'a word \<Rightarrow> 'a word \<Rightarrow> nat option" where
"find_index w v = (case find_fac w v of Some r \<Rightarrow>  Some ((length w) - (length r)) | None \<Rightarrow> None)"

lemma find_finds_factor:"find_index w v = Some r \<Longrightarrow> EX x y. w = x@v@y \<and> (length x) = r"
  unfolding find_index_def
  apply(auto simp add: length_additive option.case_eq_if split: if_splits)
  using find_returns_factor_at by blast



  
  

lemma contains_iff_find_index: "(EX r. find_index w v = Some r) \<longleftrightarrow> contains w v"
  apply(auto simp add: find_index_def)
  using contains_iff_find_fac by force+


lemma find_index_of_suffix: "find_index (drop i w) v = Some r \<and> i \<le> (length w) \<Longrightarrow> \<exists>x y. w = x@v@y \<and>  (length x) = r+i"
proof -
  assume a:"find_index (drop i w) v  = Some r \<and> i \<le> (length w)"

  then have "EX s. find_fac (drop  i w) v = Some s"   by (metis find_index_def option.collapse option.distinct(1) option.simps(4)) 
  then have "EX s. find_fac (drop i w) v = Some s \<and> r = (length (drop i w)) - (length s)"   by (metis a find_index_def option.case(2) option.inject)
  then have "EX s x y. (drop  i w) = x@v@y \<and> (length x) = (length (drop  i w))-(length s) \<and>  r = (length (drop  i w)) - (length s)"  by (metis Ex_list_of_length find_returns_factor_at)
  then have "EX s x y. (drop  i w) = x@v@y \<and> (length x) = r \<and> r = (length (drop  i w)) - (length s)"  by auto
  then have "EX s x y. (drop  i w) = x@v@y \<and> i \<le> (length w) \<and> (length x) = r \<and> r = (length (drop  i w)) - (length s)" using a  by auto
  then have "EX s x y. (\<exists>x'. w = x'@x@v@y \<and> (length x') = i) \<and> (length x) = r  \<and> r = (length (drop  i w)) - (length s)"  by (metis Words.drop_append)
  then have "EX s x y x'. w = x'@x@v@y \<and> (length x') = i \<and> (length x) = r  \<and> r = (length (drop  i w)) - (length s)" by auto
  then have "EX x y x'. w = x'@x@v@y \<and> (length x') = i \<and> (length x) = r" by auto
  then have "EX x y. w = x@v@y \<and> (length x) = r + i"  by (metis append.assoc length_additive add.commute)
  then show ?thesis   by (simp)
qed


definition replace::"'a word \<Rightarrow> 'a word \<Rightarrow> 'a word \<Rightarrow> 'a word" where
"replace w v u = (case find_index w v of Some i \<Rightarrow> (take i w)@u@(drop (i+(length v)) w) | None => w)"

lemma replace_epsilon: "replace w \<epsilon> u = u@w"
  unfolding replace_def
  apply(auto simp add: option.case_eq_if)
   apply (simp add: find_fac_epsilon find_index_def)
  by (metis append_Nil drop0 find_prefix_index_is_0 option.sel take_eq_Nil2)

lemma replace_id_if_not_contains:"\<not>contains w v \<Longrightarrow> replace w v u = w"
  unfolding replace_def
  using contains_iff_find_index  by fastforce


theorem replace_factor: "contains w v \<Longrightarrow> \<exists>x y. (w= x@v@y \<and> replace w v u = x@u@y)"
  unfolding replace_def find_index_def
  apply(auto simp add: option.case_eq_if prefix_iff_startswith)
  apply (metis contains_iff_find_fac option.distinct(1))
  by (metis append.assoc append_eq_conv_conj find_returns_factor_at length_additive)
  
  

theorem replace_first_factor: "contains w v \<Longrightarrow> \<exists>x y. replace w v u = x@u@y \<and> w = x@v@y \<and> (\<forall> x'. (length x') < (length x) \<longrightarrow> (\<nexists>y'. w=x'@v@y'))"
  apply(auto simp add: contains_iff_find_index)
  unfolding replace_def
  apply(auto simp add: option.case_eq_if contains_iff_find_index)
   apply (metis contains_iff_find_index option.distinct(1))
  proof -
    assume a: "contains w v"
    obtain aas :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" and aasa :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
      f2: "\<forall>as asa n. length (aas n asa as) = n \<and> aas n asa as @ asa @ aasa n asa as = as \<or> find_index as asa \<noteq> Some n"
      by (metis (no_types) find_finds_factor)
    obtain nn :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat" where
      f3: "find_index w v = Some (nn v w)"
      using a by (meson contains_iff_find_index)
    then have "drop (nn v w + length v) w = aasa (nn v w) v w"
      using f2 by (metis append.assoc append_eq_conv_conj length_additive)
    then show "\<exists>as asa. take (the (find_index w v)) w @ u @ drop (the (find_index w v) + length v) w = as @ u @ asa \<and> w = as @ v @ asa \<and> (\<forall>asa. length asa < length as \<longrightarrow> (\<forall>as. w \<noteq> asa @ v @ as))"
      using f3 f2 by (metis append_eq_conv_conj find_index_returns_first option.sel)
  qed
  
  
  
  

  

 

end





