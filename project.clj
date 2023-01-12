(defproject engine "1.0"
  :repositories [["jitpack" "https://jitpack.io"]] ; shapedrawer / grid2d
  :dependencies [[org.clojure/clojure "1.11.1"]
                 [nrepl "0.9.0"]
                 [org.clojure/tools.namespace "1.3.0"]
                 [com.badlogicgames.gdx/gdx                       "1.11.0"]
                 [com.badlogicgames.gdx/gdx-backend-lwjgl3        "1.11.0"]
                 ;[com.badlogicgames.gdx/gdx-lwjgl3-glfw-awt-macos "1.11.0"]
                 [com.badlogicgames.gdx/gdx-platform              "1.11.0" :classifier "natives-desktop"]
                 [space.earlygrey/shapedrawer "2.5.0"]
                 [com.github.damn/grid2d "1.0"]]
  :javac-options ["-target" "1.7" "-source" "1.7" "-Xlint:-options"]
  :java-source-paths ["src/"]
  :jvm-opts ["-XstartOnFirstThread"] ; TODO disable for packaging
  :profiles {:dev {:resource-paths ["test/resources"]}})

; TODO:

; * run warn on reflection test on all new code

; TODO separate ns asset manager for sounds & images with get-sound and get-image

; TODO android ? later ? try anroid?

; * make jar file of game (see with assets cannot list in jar with libgdx)
; -> create edn file with resoures folder content and read it -> simple

; * font only 'simple_6x8.png' at the moment
; & doesnt work in world coordinates -> add to docstring (only works with render-gui-level)

; shifting the window with the bar breaks the fitviewport


; TODO

; license

; deps.edn ?

; * documentation !

; https://www.reddit.com/r/Clojure/comments/yqj4m9/minimal_clojure_2d_game_engine_for_desktop_based/
; https://news.ycombinator.com/item?id=33531048
; https://clojurians.slack.com/archives/C066UV2MV/p1668000422880709

; TODO 2 part namespace : damn.engine

; TODO BUG
; isKeyJustPressed & isButtonJustPressed does not trigger consistently at '1.11.0' with gdx-lwjgl3-glfw-awt-macos
; is fixed when using -XstartOnFirstThread and not glfw-awt-macos
; export LEIN_JVM_OPTS='-XstartOnFirstThread'
