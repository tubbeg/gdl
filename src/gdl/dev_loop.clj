(ns ^:no-doc gdl.dev-loop
  (:require [clojure.java.io :as io]
            [gdl.utils :refer (set-var-root)]
            [nrepl.server :refer [start-server]]
            [clojure.tools.namespace.repl :refer [disable-reload! refresh-all]]))

(disable-reload!) ; keep same connection/nrepl-server up throughout refreshs

(declare app-ns
         app-fn)

(defn start-app []
  (eval `(do ; old namespace/var bindings are unloaded with refresh-all so always evaluate them fresh
          (require (quote ~app-ns))
          (~app-fn))))

(defn dev-loop []
  (start-app)
  (println "refresh-all \n" (refresh-all :after 'gdl.dev-loop/dev-loop)))

; ( I dont know why nrepl start-server does not have this included ... )
(defn save-port-file
  "Writes a file relative to project classpath with port number so other tools
  can infer the nREPL server port.
  Takes nREPL server map and processed CLI options map.
  Returns nil."
  [server]
  ;; Many clients look for this file to infer the port to connect to
  (let [port (:port server)
        port-file (io/file ".nrepl-port")]
    (.deleteOnExit ^java.io.File port-file)
    (spit port-file port)))

(defn -main [& [app-namespace app-start-fn]]
  (set-var-root #'app-ns (symbol app-namespace))
  (set-var-root #'app-fn (symbol (str app-namespace "/" app-start-fn)))

  (defonce nrepl-server (start-server))
  (save-port-file nrepl-server)
  (println "Started nrepl server on port" (:port nrepl-server))

  (dev-loop))

; Example:
; lein run -m gdl.dev-loop gdl.simple-test app
