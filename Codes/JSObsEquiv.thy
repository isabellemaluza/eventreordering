theory JSObsEquiv
imports JSRender JSLocality JSProofs JSAbsEvent
begin

(* ==========================================================================
   Observational Equivalence

   Two states are observationally equivalent when they produce the same
   rendered HTML and the same alert history.
   ========================================================================== *)

definition observable ::
  "js_state => dom_pos => html_node list * string list"
where
  "observable s pos =
     (tohtml s pos, Alerts_s s)"


definition obs_equiv ::
  "js_state => js_state => dom_pos => bool"
where
  "obs_equiv s1 s2 p =
     (tohtml s1 p = tohtml s2 p &
      Alerts_s s1 = Alerts_s s2)"


(* ==========================================================================
   Characterization through observable
   ========================================================================== *)

lemma obs_equiv_iff_observable:
  "obs_equiv s1 s2 p =
   (observable s1 p = observable s2 p)"
  by (simp add: obs_equiv_def observable_def)


(* ==========================================================================
   Basic properties
   ========================================================================== *)

lemma obs_equiv_refl:
  "obs_equiv s s p"
  by (simp add: obs_equiv_def)


lemma obs_equiv_sym:
  assumes E:
    "obs_equiv s1 s2 p"
  shows
    "obs_equiv s2 s1 p"
  using E
  by (simp add: obs_equiv_def)


lemma obs_equiv_trans:
  assumes E12:
    "obs_equiv s1 s2 p"
  and E23:
    "obs_equiv s2 s3 p"
  shows
    "obs_equiv s1 s3 p"
  using E12 E23
  by (auto simp: obs_equiv_def)


(* ==========================================================================
   State equality implies observational equivalence
   ========================================================================== *)

lemma state_eq_imp_obs_equiv:
  assumes EQ:
    "s1 = s2"
  shows
    "obs_equiv s1 s2 p"
  using EQ
  by (simp add: obs_equiv_def)


(* ==========================================================================
   Projection lemmas
   ========================================================================== *)

lemma obs_equiv_tohtml:
  assumes E:
    "obs_equiv s1 s2 p"
  shows
    "tohtml s1 p = tohtml s2 p"
  using E
  by (simp add: obs_equiv_def)


lemma obs_equiv_alerts:
  assumes E:
    "obs_equiv s1 s2 p"
  shows
    "Alerts_s s1 = Alerts_s s2"
  using E
  by (simp add: obs_equiv_def)


(* ==========================================================================
   Event absorption
   ========================================================================== *)

theorem absorbed_event_preserves_obs_equiv:
  assumes ABS:
    "make_event_handler ev obj_id s = s"
  shows
    "obs_equiv (make_event_handler ev obj_id s) s p"
  using ABS
  by (simp add: obs_equiv_def)


theorem absorption_implies_obs_stable:
  assumes ABS:
    "make_event_handler ev obj_id s = s"
  shows
    "tohtml (make_event_handler ev obj_id s) p =
     tohtml s p"
  using ABS
  by simp


theorem absorption_implies_alerts_stable:
  assumes ABS:
    "make_event_handler ev obj_id s = s"
  shows
    "Alerts_s (make_event_handler ev obj_id s) =
     Alerts_s s"
  using ABS
  by simp


(* ==========================================================================
   Idempotence gives observational equivalence
   ========================================================================== *)

theorem color_change_idempotent_obs:
  "obs_equiv
     (change_element_color i c
        (change_element_color i c s))
     (change_element_color i c s)
     p"
proof -
  have EQ:
    "change_element_color i c
       (change_element_color i c s)
     =
     change_element_color i c s"
    by (rule change_element_color_idempotent)

  show ?thesis
    using EQ
    by (simp add: obs_equiv_def)
qed


(* ==========================================================================
   Equal color-change results are observationally equivalent
   ========================================================================== *)

lemma color_change_same_result_obs:
  assumes EQ:
    "change_element_color i c1 s =
     change_element_color i c2 s"
  shows
    "obs_equiv
       (change_element_color i c1 s)
       (change_element_color i c2 s)
       p"
  using EQ
  by (simp add: obs_equiv_def)


(* ==========================================================================
   Concrete absorbed-event examples
   ========================================================================== *)

lemma absorbed_click_on_paragraph_obs:
  "obs_equiv
     (make_event_handler EvClick 1 dom_state)
     dom_state
     sample_pos"
proof -
  have ABS:
    "make_event_handler EvClick 1 dom_state =
     dom_state"
    by (rule absorb_click_on_paragraph)

  show ?thesis
    using ABS
    by (simp add: obs_equiv_def)
qed


lemma absorbed_mouseover_on_paragraph_obs:
  "obs_equiv
     (make_event_handler EvMouseOver 1 dom_state)
     dom_state
     sample_pos"
proof -
  have ABS:
    "make_event_handler EvMouseOver 1 dom_state =
     dom_state"
    by (rule absorb_mouseover_on_paragraph)

  show ?thesis
    using ABS
    by (simp add: obs_equiv_def)
qed


lemma absorbed_mouseover_on_button_obs:
  "obs_equiv
     (make_event_handler EvMouseOver 2 dom_state)
     dom_state
     sample_pos"
proof -
  have ABS:
    "make_event_handler EvMouseOver 2 dom_state =
     dom_state"
    by (rule absorb_mouseover_on_button)

  show ?thesis
    using ABS
    by (simp add: obs_equiv_def)
qed


lemma absorbed_click_on_window_obs:
  "obs_equiv
     (make_event_handler EvClick 0 dom_state)
     dom_state
     sample_pos"
proof -
  have ABS:
    "make_event_handler EvClick 0 dom_state =
     dom_state"
    by (rule absorb_click_on_window)

  show ?thesis
    using ABS
    by (simp add: obs_equiv_def)
qed


lemma absorbed_nonexistent_target_obs:
  "obs_equiv
     (make_event_handler ev 99 dom_state)
     dom_state
     sample_pos"
proof -
  have ABS:
    "make_event_handler ev 99 dom_state =
     dom_state"
    by (rule absorb_nonexistent_target)

  show ?thesis
    using ABS
    by (simp add: obs_equiv_def)
qed


(* ==========================================================================
   Executable examples
   ========================================================================== *)

value "observable dom_state sample_pos"

value
  "observable
     (make_event_handler EvClick 2 dom_state)
     sample_pos"

value
  "observable
     (change_element_color 1 ''blue'' dom_state)
     sample_pos"

end