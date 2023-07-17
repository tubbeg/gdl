(ns gdx.dev-loop
  (:require [clojure.tools.namespace.repl :refer [refresh-all]]

            ;[gdx.input-test :refer [app]]
            [gdx.simple-test :refer (app)]

            ))

; refresh-all because global state in gdx.core/initialize

(defn dev-loop []
  (app)
  (println "refresh-all \n" (refresh-all :after 'gdx.dev-loop/dev-loop)))

