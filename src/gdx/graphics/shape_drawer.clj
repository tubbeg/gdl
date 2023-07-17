(ns gdx.graphics.shape-drawer
  (:require [gdx.utils :refer (set-var-root)]
            [gdx.app :as app]
            [gdx.graphics.color :as color])
  (:import [com.badlogic.gdx.graphics Texture Pixmap Pixmap$Format Color]
           com.badlogic.gdx.graphics.g2d.TextureRegion
           [space.earlygrey.shapedrawer ShapeDrawer]))

(defn- gen-shape-drawer-texture []
  (let [pixmap (doto (Pixmap. 1 1 Pixmap$Format/RGBA8888)
                 (.setColor color/white)
                 (.drawPixel 0 0))
        texture (Texture. pixmap)]
    (.dispose pixmap)
    texture))

(app/defmanaged ^{:private true :tag Texture :dispose true} shape-drawer-texture
  (gen-shape-drawer-texture))

(defn- ->ShapeDrawer [batch]
  (ShapeDrawer. batch (TextureRegion. shape-drawer-texture 0 0 1 1)))

(declare ^ShapeDrawer shape-drawer)

(defn ^:no-doc create [batch]
  (set-var-root #'shape-drawer (->ShapeDrawer batch)))

(defn- set-shapes-color [^Color color]
  (.setColor shape-drawer color))

(defn set-default-line-width [width]
  (.setDefaultLineWidth shape-drawer (float width)))

(defmacro with-shape-drawer-line-width [width & exprs]
  `(let [old-line-width# (.getDefaultLineWidth shape-drawer)]
     (set-default-line-width (* ~width old-line-width#))
     ~@exprs
     (set-default-line-width old-line-width#)))

(defn draw-ellipse [[x y] radius-x radius-y color]
  (set-shapes-color color)
  (.ellipse shape-drawer (float x) (float y) (float radius-x) (float radius-y)))

(defn fill-ellipse [[x y] radius-x radius-y color]
  (set-shapes-color color)
  (.filledEllipse shape-drawer (float x) (float y) (float radius-x) (float radius-y)))

(defn draw-circle [[x y] radius color]
  (set-shapes-color color)
  (.circle shape-drawer (float x) (float y) (float radius)))

(defn fill-circle [[x y] radius color]
  (set-shapes-color color)
  (.filledCircle shape-drawer (float x) (float y) (float radius)))

(defn- degree->radians [degree] ; TODO not here
  (* degree (/ (Math/PI) 180)))

(defn draw-arc [[centre-x centre-y] radius start-angle degree color]
  (set-shapes-color color)
  (.arc shape-drawer centre-x centre-y radius start-angle (degree->radians degree)))

(defn draw-sector [[centre-x centre-y] radius start-angle degree color]
  (set-shapes-color color)
  (.sector shape-drawer centre-x centre-y radius start-angle (degree->radians degree)))

(defn draw-rect
  ([[x y w h] color]
   (draw-rect x y w h color))
  ([x y w h color]
   (set-shapes-color color)
   (.rectangle shape-drawer x y w h)))

(defn fill-rect
  ([[x y w h] color]
   (fill-rect x y w h color))
  ([x y w h color]
   (set-shapes-color color)
   (.filledRectangle shape-drawer (float x) (float y) (float w) (float h))))

(defn draw-line
  ([[x y] [ex ey] color]
   (draw-line x y ex ey color))
  ([x y ex ey color]
   (set-shapes-color color)
   (.line shape-drawer (float x) (float y) (float ex) (float ey))))

(defn draw-grid
  [leftx bottomy gridw gridh cellw cellh color]
  (let [w (* gridw cellw)
        h (* gridh cellh)
        topy (+ bottomy h)
        rightx (+ leftx w)]
    (doseq [idx (range (inc gridw))
            :let [linex (+ leftx (* idx cellw))]]
           (draw-line linex topy linex bottomy color))
    (doseq [idx (range (inc gridh))
            :let [liney (+ bottomy (* idx cellh))]]
           (draw-line leftx liney rightx liney color))))
