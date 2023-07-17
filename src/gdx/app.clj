(ns gdx.app
  (:require [gdx.utils :refer (set-var-root)])
  (:import [com.badlogic.gdx Application Gdx]
           com.badlogic.gdx.utils.Disposable))

; app/create -> lwjgl in here
; app/destroy instead of exit
; screen/game also in here (public API)
; app/defscreen

(def ^:private on-create-fns  [])
(def ^:private on-destroy-fns [])

(defmacro on-create  [& exprs] `(alter-var-root #'on-create-fns  conj (fn [] ~@exprs)))
(defmacro on-destroy [& exprs] `(alter-var-root #'on-destroy-fns conj (fn [] ~@exprs)))

(defn ^:no-doc call-on-create-fns!  [] (doseq [f on-create-fns]  (f)))
(defn ^:no-doc call-on-destroy-fns! [] (doseq [f on-destroy-fns] (f)))

(defn ^:no-doc dispose [^Disposable obj] (.dispose obj))

; def docs:
;  Creates and interns a global var with the name
;  of symbol in the current namespace (*ns*) or locates such a var if
;  it already exists.  If init is supplied, it is evaluated, and the
;  root binding of the var is set to the resulting value.  If init is
;  not supplied, the root binding of the var is unaffected.

(defmacro defmanaged [symbol init]
  `(do
    (declare ~symbol)
    (let [var# (var ~symbol)]
      (on-create (set-var-root var# ~init))
      (on-destroy (when (:dispose (meta var#)) (dispose ~symbol))))))

(defmanaged ^Application app Gdx/app)

(defn exit [] ; destroy
  (.exit app))

(defmacro post-runnable [& exprs]
  `(.postRunnable app (fn [] ~@exprs)))

