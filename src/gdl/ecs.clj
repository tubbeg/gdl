(ns gdl.ecs
  (:require [gdl.session :as session]))

(defmacro defsystem [symbol]
  `(def ~symbol {}))

(defn extend-system [system-var c f]
  (alter-var-root system-var assoc c f))

(defmacro defcomponent [c & system-fns]
  `(do
    ~@(for [[system & fn-body] system-fns
            :let [fn-name (symbol (str (name system) "X" (name c)))
                  fn-form `(fn ~fn-name ~@fn-body)]]
        (list `extend-system (list 'var system) c fn-form))))

(defn apply-system! [system entity]
  (let [entity* @entity]
    (doseq [[ctype f] system
            :let [v (ctype entity*)]
            :when v]
      (f entity)))) ; TODO pass component /// pure

(def ^:private ids->entities (atom nil))
(def ^:private removelist (atom nil))

(session/defstate state
  (load!  [_ data]
   (reset! ids->entities {})
   (reset! removelist #{}))
  (serialize [_])
  (initial-data [_]))

(defn get-entity [id]
  (get @ids->entities id))

(defn exists? [entity]
  (get-entity (:id @entity)))

(defsystem on-create-entity)
(defsystem after-create-entity)
(defsystem on-destroy-entity)

(defcomponent :id
  (on-create-entity [entity]
    (swap! ids->entities assoc (:id @entity) entity))
  (on-destroy-entity [entity]
    (swap! ids->entities dissoc (:id @entity))))

(let [cnt (atom 0)]
  (defn- unique-number! []
    (swap! cnt inc)))

(defn create-entity! [properties]
  {:pre [(not (contains? properties :id))]}
  (let [entity (atom (assoc properties :id (unique-number!)))]
    (apply-system! on-create-entity    entity)
    (apply-system! after-create-entity entity)
    entity))

(defcomponent :parent
  (on-create-entity [child]
   (let [parent (:parent @child)]
     (assert (exists? parent))
     (if-let [children (:children @parent)]
       (do
        (assert (not (contains? children child)))
        (swap! parent update :children conj child))
       (swap! parent assoc :children #{child}))))
  (on-destroy-entity [child]
   (let [parent (:parent @child)]
     (when (exists? parent)
       (let [children (:children @parent)]
         (assert (contains? children child))
         (if (= children #{child})
           (swap! parent dissoc :children)
           (swap! parent update :children disj child)))))))

(defn add-to-removelist [entity]
  (swap! removelist conj entity))

; first destroy entity, then not necessary for children to remove themself anymore @ parent :children
(defn destroy-to-be-removed-entities []
  (doseq [entity @removelist
          entity (if-let [children (:children @entity)]
                   (cons entity children)
                   [entity])
          :when (exists? entity)]
    (apply-system! on-destroy-entity entity))
  (reset! removelist #{}))

;;
;;
;; Update system (separate file/ns ?)
;;
;;

; # Why do we use a :blocks counter and not a boolean?
; Different effects can stun/block for example :movement component
; and if we remove the effect, other effects still need to be there
; so each effect increases the :blocks-count by 1 and decreases them after the effect ends.

(defn- blocked? [component]
  (when-let [blocks-count (:blocks component)]
    (assert (and (integer? blocks-count)
                 (>= blocks-count 0)))
    (> blocks-count 0)))

(defn- update-speed [component]
  (or (:update-speed component) 1))

; with ecs/ prefix could make them shorter maybe
(defsystem update-component)
(defsystem update-entity*)
(defsystem update-entity!)

(def ^:private system-apply-fns
  {#'update-component (fn [ctype f entity delta] (swap! entity update ctype f delta))
   #'update-entity*   (fn [_     f entity delta] (swap! entity f delta))
   #'update-entity!   (fn [_     f entity delta] (f entity delta))})

; TODO fuck update-entity! shadowed down there ..
; TODO call 'tick' ? because delta
; ecs/tick*c tick*e tick*!
; 3 types of systems, extra args are delta !
; modifiers are also systems !!

; strange that update-entity! doesnt care about the ctype
; maybe it is not meant to be a component function but rather entity-wide function?
; or system

; TODO similar to apply-system! !!!!!
; also check render .. !
(defn- update-entity!* [entity delta]
  (doseq [[system apply-fn] system-apply-fns
          [ctype f] @system
          :let [component (ctype @entity)] ; TODO if has implementation, not if key not falsey ... later ...
          :when component
          :let [delta (->> (update-speed component) (* delta) int (max 0))]
          ; TODO what if speed =0 ??
          :when (not (blocked? component))]
    (try
     (apply-fn ctype f entity delta)
     (catch Throwable t
       (println "Entity id " (:id @entity))
       (throw t)))))

(defn update-entities! [entities delta]
  (doseq [entity entities]
    (update-entity!* entity delta)))
