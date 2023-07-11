(ns gdx.repl
  (:require [gdx.dev-loop :refer [dev-loop]]
            [nrepl.server :refer [start-server]]
            [clojure.tools.namespace.repl :refer [set-refresh-dirs disable-reload!]]))

; dev-loop is a separate ns & here disable-reload!
; because otherwise the nrepl-server gets lost at each reload & throws an error
; & have to connect again
; but maybe I can have this two in one file ? not sure if that works with refresh
(disable-reload!)

(defn -main []
  (defonce nrepl-server (start-server :port 7888))
  (println "Started nrepl server on port 7888.")
  ; TODO set all dirs ...
  #_(set-refresh-dirs (clojure.java.io/file "src/gdx/")
                    (clojure.java.io/file "src/utils/"))
  (dev-loop))
