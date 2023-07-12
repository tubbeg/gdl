(ns gdx.ecs
  (:require [gdx.state :as state]))

(def ctype-fns {})

; TODO defcomponentfn ?
(defmacro defctypefn [fnkey ctype & fn-body]
  `(let [ctype-fn# (fn ~(symbol (str (name fnkey) "-" (name ctype)))
                     ~@fn-body)]
    (alter-var-root #'ctype-fns assoc-in [~fnkey ~ctype] ctype-fn#)
    [~fnkey ~ctype]))

; TODO call-component-fns! ?
(defn call-ctype-fns! [fn-key entity]
  (doseq [[ctype f] (select-keys (get ctype-fns fn-key)
                                 (keys @entity))
          :when (ctype @entity)]
    (f entity)))

(def ^:private ids->entities (atom nil))
(def ^:private removelist (atom nil))

(def state (reify state/State
             (load! [_ _]
               (reset! ids->entities {})
               (reset! removelist #{}))
             (serialize [_])
             (initial-data [_])))

(defn get-entity [id]
  (get @ids->entities id))

; TODO @entity & set nil?
(defn exists? [entity]
  (get-entity (:id @entity)))

(let [cnt (atom 0)]
  (defn- unique-number! []
    (swap! cnt inc)))

(defctypefn :on-create-entity :id [entity]
  (swap! ids->entities assoc (:id @entity) entity))

(defctypefn :on-destroy-entity :id [entity]
  (swap! ids->entities dissoc (:id @entity)))

(defrecord Entity [id
                   is-player
                   position
                   width
                   height
                   half-width
                   half-height
                   is-solid
                   speed
                   hp
                   mana
                   z-order])

(defn create-entity! [properties]
  {:pre [(not (contains? properties :id))]}
  (let [entity (atom
                (assoc (map->Entity properties)
                       :id (unique-number!)))]
    (call-ctype-fns! :on-create-entity    entity)
    (call-ctype-fns! :after-create-entity entity)
    entity))

(defctypefn :on-create-entity :parent [child]
  (let [parent (:parent @child)]
    (assert (exists? parent))
    (if-let [children (:children @parent)]
      (do
       (assert (not (contains? children child)))
       (swap! parent update :children conj child))
      (swap! parent assoc :children #{child}))))

(defctypefn :on-destroy-entity :parent [child]
  (let [parent (:parent @child)]
    (when (exists? parent)
      (let [children (:children @parent)]
        (assert (contains? children child))
        (if (= children #{child})
          (swap! parent dissoc :children)
          (swap! parent update :children disj child))))))

; the point of the removelist is to not destroy entities during
; the update loop, because their reference will still be in the sequence of to-updated-entities
; so we add them to removelist and at the end of a frame destroy them
; -> we could just check if exists? or :is-destroyed? though
; but maybe better not remove entities during a frame.
; but then in the same frame they can die & still attack ? or heal also
; TODO '!'
(defn add-to-removelist [entity]
  (swap! removelist conj entity))

; first destroy entity, then not necessary for children to remove themself anymore @ parent :children
(defn destroy-to-be-removed-entities []
  (doseq [entity @removelist
          entity (if-let [children (:children @entity)]
                   (cons entity children)
                   [entity])
          :when (exists? entity)]
    (call-ctype-fns! :on-destroy-entity entity)
    ; TODO (reset! entity nil) ?
    )
  (reset! removelist #{}))
