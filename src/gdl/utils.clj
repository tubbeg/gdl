(ns gdl.utils
  (:import com.badlogic.gdx.utils.Disposable))

(defn set-var-root [v value]
  (alter-var-root v (constantly value)))


; TODO gdl.event  ?
; event/on :app/create
; event/fire! :app/create
; event/add-listener :app-create #'foo-fn) ; var so can redef ? would that work ?

(def events->listeners {})

; TODO could add (defevent :foo) -> which adds it to events->listeners
; and @ add-listener check (@ compile time?) if the event exists....

(defn add-listener [event listener]
  (alter-var-root #'events->listeners update event
                  #(conj (or % []) listener))
  nil)

(defmacro on [event & exprs]
  `(add-listener ~event
                 (fn []
                   ; TODO !
                   (println "On" (quote ~event) " exprs:" (quote ~exprs))
                   ~@exprs)))

(defn fire-event! [event]
  (doseq [listener (get events->listeners event)]
    (listener)))

(defn dispose [^Disposable obj]
  (.dispose obj))
