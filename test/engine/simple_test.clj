(ns engine.simple-test
  (:require [engine.tiled :as tiled]
            [engine.graphics :refer :all]
            [engine.input :refer :all]
            [engine.core :refer :all]))

(on-create
 (def sheet (spritesheet "items.png" 16 16))
 (def sprite (get-sprite sheet [5 4])))

(defn map-content []
  ;(draw-grid 0 0 24 18 1 1 (darker white 0.5))
  ;(draw-line 10 10 12 12 red)
  ;(draw-centered-image test-image-1 [12 6])
  ;(fill-rect 12 6 1 1 white)
  )

(defn gui-render []
  (draw-string 0 0 (get-fps))

  (let [[x y] (map #(format "%.2f" %) (map-coords))
        [gx gy] (mouse-coords)
        [sx sy] (get-mouse-pos)]
    (render-readable-text 0 60
                          {:shift true}
                          (str "Map x " x)
                          (str "Map y " y)
                          (str "GUI x " gx)
                          (str "GUI y " gy)
                          (str "Screen X" sx)
                          (str "Screen Y" sy)))

  (let [[x y] (mouse-coords)]
    (render-readable-text x y
                          {:centerx true :centery true :shift true}
                          "Colored Font test"
                          red
                          "red"
                          blue
                          "blue"
                          yellow
                          "yellow")))

(def ingame-gamestate
  (reify GameScreen
    (show [_]
      (def tiled-map (tiled/load-map "example.tmx"))) ; TODO init ...
    (destroy [_]
      (tiled/dispose tiled-map))
    (render [_]
      (render-map tiled-map
                  (fn [color x y] white)
                  [11 13]
                  [:ground :details :entities])
      (render-map-level map-content)
      (render-gui-level gui-render))
    (update-screen [_ delta])))

(defn app []
  (start-app :full-screen false
             :title "engine demo"
             :window-width 1440
             :window-height 900
             :viewport-width 360
             :viewport-height 225
             :assets-folder "test/resources/"
             :game-screens {:main ingame-gamestate}))
