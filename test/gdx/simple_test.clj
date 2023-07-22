(ns gdx.simple-test
  (:require [gdx.backends.lwjgl3 :as lwjgl3]
            [gdx.app :as app]
            [gdx.game :as game]
            [gdx.assets :as assets]
            [gdx.graphics :as g]
            [gdx.graphics.font :as font]
            [gdx.input :as input]))

(font/def-font bmfont16 "exocet/films.EXL_____.ttf" 16)

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
                     "Screen Y" sy)
        y 300]
    (g/draw-text (str "default-font\n" the-str) 0 y)
    (font/draw-text bmfont16 (str "exl-font\n" the-str) 300 y)))

(defn render []
  (render-mouse-coordinates))

(game/defscreen screen
  :show (fn [])
  :render (fn [] (g/render-gui render))
  :destroy (fn [])
  :update (fn [delta]))

(defn app []
  (lwjgl3/create-app (game/create {:main screen})
                     {:title "gdx demo"
                      :width 800
                      :height 600
                      :full-screen false}))
