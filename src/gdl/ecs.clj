(ns gdl.ecs
  (:require [gdl.session :as session]))

(def ctype-fns {})

; TODO next step -> systems as protocols (compile time check args)
; and separate vars with only their own (ctype->f)
; and application fn
; (apply-system, update-system, render-system so far only ?)

; also: all -component / -entity* and / -! functions
; make available for all systems
; e.g. on-stun*c only changes sth there...

(defmacro defctypefn [fnkey ctype & fn-body]
  `(let [ctype-fn# (fn ~(symbol (str (name fnkey) "-" (name ctype)))
                     ~@fn-body)]
    (alter-var-root #'ctype-fns assoc-in [~fnkey ~ctype] ctype-fn#)))

(defmacro defcomponent [kw & system-impls]
  `(do
    ~@(for [[system-name & fnbody] system-impls]
        (do
         (apply list `defctypefn (keyword (name system-name)) kw fnbody)))))

(defn call-ctype-fns! [fn-key entity]
  (let [entity* @entity]
    (doseq [[ctype f] (get ctype-fns fn-key)
            ; TODO we probably want the component data and also 3 kind of applications?
            :when (ctype entity*)]
      (f entity))))

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
    (call-ctype-fns! :on-create-entity    entity)
    (call-ctype-fns! :after-create-entity entity)
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
    (call-ctype-fns! :on-destroy-entity entity))
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

(def ^:private system-fns
  {:update-component (fn [ctype f entity delta] (swap! entity update ctype f delta))
   :update-entity*   (fn [_     f entity delta] (swap! entity f delta))
   :update-entity!   (fn [_     f entity delta] (f entity delta))})

; strange that update-entity! doesnt care about the ctype
; maybe it is not meant to be a component function but rather entity-wide function?
; or system

(defn- update-entity! [entity delta]
  (doseq [[system-k system-fn] system-fns
          [ctype f] (system-k ctype-fns)
          :let [component (ctype @entity)] ; TODO if has implementation, not if key not falsey ... later ...
          :when component
          :let [delta (->> (update-speed component) (* delta) int (max 0))]
          ; TODO what if speed =0 ??
          :when (not (blocked? component))]
    (try
     (system-fn ctype f entity delta)
     (catch Throwable t
       (println "Entity id " (:id @entity))
       (throw t)))))

(defn update-entities! [entities delta]
  (doseq [entity entities]
    (update-entity! entity delta)))
