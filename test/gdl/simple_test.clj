(ns gdl.simple-test
  (:require [gdl.backends.lwjgl3 :as lwjgl3]
            [gdl.game :as game]
            [gdl.graphics :as g]
            [gdl.graphics.freetype :as freetype]
            [gdl.input :as input]))

(freetype/def-font bmfont16 "exocet/films.EXL_____.ttf" 16)

; TODO use @ cdq/game/ui/debug-window
(defn render-mouse-coordinates []
  (let [[x y] (map #(format "%.2f" %) (g/map-coords))
        [gx gy] (g/mouse-coords)
        [sx sy] (input/get-mouse-pos) ; TODO same as mouse-coords ?
        the-str (str "Map x " x "\n"
                     "Map y " y "\n"
                     "GUI x " gx "\n"
                     "GUI y " gy "\n"
                     "Screen X" sx "\n"
                     "Screen Y" sy)]
    (g/draw-text {:font nil
                  :text (str "default-font\n" the-str)
                  :x sx,:y sy,:h-align nil,:up? true})
    (g/draw-text {:font bmfont16
                  :text (str "exl-font\n" the-str)
                  :x sx,:y sy,:h-align :left,:up? false})))

(defn render []
  (render-mouse-coordinates))

(game/defscreen screen
  :show (fn [])
  :render (fn [] (g/render-gui render))
  :destroy (fn [])
  :update (fn [delta]))

(defn app []
  (lwjgl3/create-app (game/create {:main screen})
                     {:title "gdl demo"
                      :width 800
                      :height 600
                      :full-screen false}))
