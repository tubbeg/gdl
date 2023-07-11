(ns gdx.dev-loop
  (:require [clojure.tools.namespace.repl :refer [refresh-all]]

            ;[gdx.input-test :refer [app]]
            [gdx.simple-test :refer (start-app)]

            ))

; refresh-all because global state in gdx.core/initialize

(defn dev-loop []
  (start-app)
  (refresh-all :after 'gdx.dev-loop/dev-loop))
