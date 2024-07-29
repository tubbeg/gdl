(def libgdx-version "1.12.0")

(defproject com.github.damn/gdl "main-SNAPSHOT"
  :repositories [["jitpack" "https://jitpack.io"]] ; shapedrawer / grid2d
  :dependencies [[org.clojure/clojure "1.11.1"]
                 [com.github.damn/core.component "600ea8e"]
                 ; only @ dev profile ?
                 [nrepl "0.9.0"]
                 [org.clojure/tools.namespace "1.3.0"]
                 [org.clj-commons/pretty "2.0.1"]
                 [com.badlogicgames.gdx/gdx                       ~libgdx-version]
                 [com.badlogicgames.gdx/gdx-platform              ~libgdx-version :classifier "natives-desktop"]
                 [com.badlogicgames.gdx/gdx-backend-lwjgl3        ~libgdx-version]
                 ;[com.badlogicgames.gdx/gdx-lwjgl3-glfw-awt-macos ~libgdx-version]
                 [com.badlogicgames.gdx/gdx-freetype              ~libgdx-version]
                 [com.badlogicgames.gdx/gdx-freetype-platform     ~libgdx-version :classifier "natives-desktop"]
                 [com.kotcrab.vis/vis-ui "1.5.2"]
                 [space.earlygrey/shapedrawer "2.5.0"]]
  :javac-options ["-target" "1.8" "-source" "1.8" "-Xlint:-options"] ; TODO why ? libgdx ?
  :java-source-paths ["src-java"]
  :profiles {:dev {:resource-paths ["test/resources"]}}
  :plugins [[lein-codox "0.10.8"]
            [lein-hiera "2.0.0"]]
  :codox {:source-uri "https://github.com/damn/gdl/blob/main/{filepath}#L{line}"}
  :global-vars {*warn-on-reflection* true
                ;*unchecked-math* :warn-on-boxed
                }
  :aliases {"dev" ["run" "-m" "gdl.backends.libgdx.dev" "gdl.simple-test" "app"]})

;; TODO dev
; - clojure.pprint => https://github.com/AbhinavOmprakash/snitch
; - intern them through user.clj somehow into clojure.core
; -XstartOnFirstThread
; - set repl ...
