(ns gdl.simple-test
  (:require [x.x :refer [defcomponent]]
            [gdl.lc :as lc]
            [gdl.app :as app]
            [gdl.files :as files]
            [gdl.game :as game]
            [gdl.graphics.world :as world]
            [gdl.graphics.gui :as gui]
            [gdl.graphics.font :as font]
            [gdl.graphics.freetype :as freetype]))

(declare bmfont16)

(defn- gen-font []
  (freetype/generate (files/internal "exocet/films.EXL_____.ttf")
                     16))

(defn render-mouse-coordinates []
  (let [[wx wy] (map #(format "%.2f" %) (world/mouse-position))
        [gx gy] (gui/mouse-position)
        the-str (str "World x " wx "\n"
                     "World y " wy "\n"
                     "GUI x " gx "\n"
                     "GUI y " gy "\n")]
    (font/draw-text {:font nil
                     :text (str "default-font\n" the-str)
                     :x gx,:y gy,:h-align nil,:up? true})
    (font/draw-text {:font bmfont16
                     :text (str "exl-font\n" the-str)
                     :x gx,:y gy,:h-align :left,:up? false})))

(def my-screen
  (reify app/Screen
    (show [_])
    (render [_]
      (game/render-gui
       render-mouse-coordinates))
    (tick [_ delta])))

; !
; TODO lein template
; application config
; config/application.edn
; => window config
; => screens / ns-components ? same ? gets loaded automatically?
; no more 'start' ns => remove ! config files?

(defcomponent *ns* _
  (lc/create [_]
    (.bindRoot #'bmfont16 (gen-font)) )
  (lc/dispose [_]
    (.dispose bmfont16) ))

(defn app []
  (game/start {:screens {:my-screen my-screen}
               :tile-size 48
               :window {:title "gdl demo"
                        :width 800
                        :height 600
                        :full-screen false}
               :log-lc? true
               :ns-components [[:gdl.simple-test]]}))
