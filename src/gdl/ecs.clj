(ns gdl.ecs
  (:require [x.x :refer :all]
            [gdl.session :as session]))

(def ^:private ids->rs (atom nil))

(defn get-entity [id] (get @ids->rs id))
(defn exists? [r] (get-entity (:id @r)))

(session/defstate state
  (load!  [_ data]
    (reset! ids->rs {}))
  (serialize [_])
  (initial-data [_]))

(defsystems create-systems  [create  create-e  create! ])
(defsystems destroy-systems [destroy destroy-e destroy!])

(let [cnt (atom 0)] ; TODO reset cnt every session ?
  (defn- unique-number! []
    (swap! cnt inc)))

(extend-component :id
  (create [_ _] (unique-number!)) ; TODO precondition (nil? id)
  (create!  [_ r] (swap! ids->rs assoc  (:id @r) r))
  (destroy! [_ r] (swap! ids->rs dissoc (:id @r))))

(defsystem after-create! [c r])

(defn create-entity! [e]
  {:pre [(not (contains? e :id))]}
  (->> (assoc e :id nil)
      atom
      (!x! create-systems)
      (doseq-r! after-create!)))

; TODO => use destroy! callback ! for children (just mark as :destroyed? ?) one frame later?
(defn destroy-to-be-removed-entities! []
  (doseq [r (filter (comp :destroyed? deref) (vals @ids->rs))
          r (if-let [children (:children @r)]
              (cons r children)
              [r])
          :when (exists? r)]
    (!x! destroy-systems r)))

(defsystems tick-systems
  [tick tick-e tick!]
  :extra-params [delta])

(defn tick-entities! [rs delta]
  (doseq [r rs]
    (!x! tick-systems r delta)))

; # Why do we use a :blocks counter and not a boolean?
; Different effects can stun/block for example :movement component
; and if we remove the effect, other effects still need to be there
; so each effect increases the :blocks-count by 1 and decreases them after the effect ends.
(defn- blocked? [v]
  (when-let [cnt (:blocks v)]
    (assert (and (integer? cnt)
                 (>= cnt 0))) ; TODO pos??
    (> cnt 0)))

(defn- update-speed [v] (or (:update-speed v) 1)) ; TODO delta-mult

#_(([[
                delta (->> (update-speed component) (* delta) int (max 0))]
          :when (not (blocked? component))]
  ))


; TODO check (if map) blocks/delta-mult for each component
; => wrap all the defmethods ... ? how 2 do that ?

; also: why do all components have to be maps ... ?
; because I dont have a component 'type' which holds a 'value'
; but its not a problem to make anything which should be blocked/changed the speed into a map
; then it must be important enough ->
; actually the idea was to block/change speed more fine-grained not on a whole component!
; => so move it out of here !
; not worth the hassle right now also unintended side effects when changing component stuff


; TODO
; * can get rid of update-speed => use directly move-speed,attack-speed,cast-speed etc. !
; * blocked - only movment/skill so far @ sleeping / stun
; => more specific ? block attacks
; -> in case of stun I STOP attacks and FREEZE (whole entity?)

; same issue of 'blocking' , with checking here @ movement not :is-active?


; stun/active-skill/sleeping => no movement (can be different for skill)
; stun/sleeping => no skill usage (cooldown?)

; these are basically COMPONENT SYSTEM MODIFIERS








; TODO maybe not necessary when using just components ?
; stun-effect == in effects
; show-string-effect => also in effects/children?
; -> render will render all children too ??
; -> children can have z-order (like an entity itself ?)

; =? also move together with other parent code @ update posi ( or i dont know what a parent is anymore)

; so complicated the parent/children code !
; just make everything with components !

; I need separate z-order for each component
; and entity-wide

; so I take lowest entities - lowest-components
; etc. build vector with certain order [e-z-order & c-z-order]
; e-z-order because entity might 'fly'
; or I can just add new layers and in case of flying update all z-orders ?
; only 1 level deep components at the moment so simple, keep simple
; or keep functions, z-order is behavior ??

(extend-component :parent
  (create! [_ child]
    (let [parent (:parent @child)]
      (assert (exists? parent))
      (if-let [children (:children @parent)]
        (do
         (assert (not (contains? children child)))
         (swap! parent update :children conj child))
        (swap! parent assoc :children #{child}))))
  (destroy! [_ child]
    (let [parent (:parent @child)]
      (when (exists? parent)
        (let [children (:children @parent)]
          (assert (contains? children child))
          (if (= children #{child})
            (swap! parent dissoc :children)
            (swap! parent update :children disj child)))))))

; first destroy entity, then not necessary for children to remove themself anymore @ parent :children
