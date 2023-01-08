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
  :jvm-opts ["-XstartOnFirstThread"]
  :profiles {:dev {:resource-paths ["test/resources"]}})

; TODO:

; * make jar file of game (see with assets cannot list in jar with libgdx)

; * font only 'simple_6x8.png' at the moment
; & doesnt work in world coordinates.

; shifting the window with the bar breaks the fitviewport
