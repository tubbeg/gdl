(ns gdl.graphics.gui
  (:require [x.x :refer [defmodule]]
            [gdl.lc :as lc]
            [gdl.graphics :as g]
            [gdl.graphics.viewport :as viewport]
            gdl.render)
  (:import com.badlogic.gdx.graphics.OrthographicCamera
           [com.badlogic.gdx.utils.viewport Viewport FitViewport]))

(def unit-scale 1)

(declare ^OrthographicCamera camera
         ^Viewport viewport)

(defmodule _
  (lc/create [_]
    (.bindRoot #'camera   (OrthographicCamera.))
    (.bindRoot #'viewport (FitViewport. (g/screen-width)
                                        (g/screen-height)
                                        camera))))

(defn mouse-position []
  (mapv int (viewport/unproject-mouse-posi viewport)))

(defn viewport-width  [] (.getWorldWidth  viewport))
(defn viewport-height [] (.getWorldHeight viewport))

(defn render [batch renderfn]
  (gdl.render/render-with batch unit-scale camera renderfn))
