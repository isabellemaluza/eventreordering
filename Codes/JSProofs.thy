theory JSProofs
imports JSRender JSQuerySelector
begin

(* NOTA: no texto original, pelo menos dois teoremas vieram sem o "="
   entre os dois lados da igualdade (efeito colateral de ter colado de
   um editor que "engoliu" o caractere). Isso foi corrigido abaixo.
   O teorema que falava de "apply_output (OutChangeColor ...)" foi
   reescrito em termos de change_element_color, já que a camada
   js_output/apply_output foi eliminada (ver JSRender). *)

lemma update_prop_idempotent:
  "update_prop k v (update_prop k v ps) = update_prop k v ps"
proof (induct ps)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  then show ?case by (cases p) (auto split: if_split)
qed

lemma load_after_write:
  "load_object obj_id (write_object obj_id v state) = Some v"
  by (simp add: load_object.simps write_object.simps)

lemma write_object_idempotent:
  "write_object obj_id v (write_object obj_id v state) = write_object obj_id v state"
  by (simp add: write_object.simps)

lemma find_filter_none:
  "find (%(k,v). k = obj_id) (filter (%(k,_). k ~= obj_id) xs) = None"
  by (induct xs) auto

(* Trocar a cor do mesmo elemento para a mesma cor duas vezes é o mesmo
   que trocar uma vez. *)
theorem change_element_color_idempotent:
  "change_element_color obj_id color (change_element_color obj_id color state)
   = change_element_color obj_id color state"
proof (cases "load_object obj_id state")
  case None
  then show ?thesis by simp
next
  case (Some v)
  then show ?thesis
  proof (cases v)
    case (VDOMElement tag props)

    define props1 where "props1 = update_prop ''color'' (VString color) props"
    define state1 where "state1 = write_dom_element obj_id tag props1 state"

    have step1: "change_element_color obj_id color state = state1"
      using Some VDOMElement unfolding props1_def state1_def by simp

    have Hload1: "load_object obj_id state1 = Some (VDOMElement tag props1)"
      unfolding state1_def by (simp add: write_dom_element.simps load_after_write)

    define props2 where "props2 = update_prop ''color'' (VString color) props1"
    define state2 where "state2 = write_dom_element obj_id tag props2 state1"

    have step2: "change_element_color obj_id color state1 = state2"
      using Hload1 unfolding props2_def state2_def by simp

    have props_eq: "props2 = props1"
      unfolding props2_def props1_def by (simp add: update_prop_idempotent)

    have state_eq: "state2 = state1"
      unfolding state2_def props_eq state1_def
      by (simp add: write_dom_element.simps write_object_idempotent)

    show ?thesis by (simp only: step1 step2 state_eq)
  qed (use Some in simp_all)
qed

theorem write_object_last_write_wins:
  "load_object obj_id (write_object obj_id b (write_object obj_id a state)) = Some b"
  by (simp add: load_object.simps write_object.simps)

theorem write_dom_element_idempotent:
  "write_dom_element obj_id tag props (write_dom_element obj_id tag props state)
   = write_dom_element obj_id tag props state"
  by (simp add: write_dom_element.simps write_object_idempotent)

theorem insert_remove_absent:
  "load_object obj_id (remove_object obj_id (insert_dom_element obj_id tag props state)) = None"
  by (simp add: load_object.simps remove_object.simps insert_dom_element.simps
                write_object.simps find_filter_none)

theorem remove_insert_present:
  "load_object obj_id (insert_dom_element obj_id tag props (remove_object obj_id state))
   = Some (VDOMElement tag props)"
  by (simp add: load_object.simps insert_dom_element.simps write_object.simps)

(* --- demonstrações (value), agora todas sobre dom_state / change_element_color --- *)

value "change_element_color 1 ''blue'' dom_state"
value "change_element_color 1 ''blue'' (change_element_color 1 ''blue'' dom_state)"
value "change_element_color 1 ''blue'' (change_element_color 1 ''blue'' dom_state)
       = change_element_color 1 ''blue'' dom_state"

value "write_dom_element 1 ''p'' [(''text'', VString ''Oi''), (''color'', VString ''blue'')] dom_state"
value "write_dom_element 1 ''p'' [(''text'', VString ''Oi''), (''color'', VString ''blue'')]
         (write_dom_element 1 ''p'' [(''text'', VString ''Oi''), (''color'', VString ''blue'')] dom_state)"

value "load_object 1 (write_object 1 (VString ''b'') (write_object 1 (VString ''a'') dom_state))"
value "load_object 1 (write_dom_element 1 ''p'' [(''color'', VString ''blue'')]
         (write_dom_element 1 ''p'' [(''color'', VString ''red'')] dom_state))"
value "load_object 1 dom_state"

end
