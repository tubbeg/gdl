(ns gdl.game
  (:require [gdl.lc :as lc]
            [gdl.gdx :as gdx]
            [gdl.graphics :as g]
            [gdl.graphics.color :as color]
            [gdl.graphics.gui :as gui]
            [gdl.graphics.world :as world]
            [gdl.graphics.unit-scale :refer [*unit-scale*]]
            [gdl.graphics.shape-drawer :as shape-drawer]
            [gdl.graphics.batch :refer [batch]]
            [gdl.backends.lwjgl3 :as lwjgl3])
  (:import [com.badlogic.gdx Gdx Game]
           com.badlogic.gdx.utils.ScreenUtils
           com.badlogic.gdx.graphics.OrthographicCamera))

(defn- on-resize [w h]
  (let [center-camera? true]
    (.update gui/viewport   w h center-camera?)
    (.update world/viewport w h center-camera?)))

(defn- fix-viewport-update
  "Sometimes the viewport update is not triggered."
  []
  (when-not (and (= (.getScreenWidth  gui/viewport) (g/screen-width))
                 (= (.getScreenHeight gui/viewport) (g/screen-height)))
    (on-resize (g/screen-width) (g/screen-height))))

(defn- render-with [unit-scale ^OrthographicCamera camera renderfn]
  (binding [*unit-scale* unit-scale]
    (shape-drawer/set-line-width! *unit-scale*)
    (.setColor batch color/white) ; fix scene2d.ui.tooltip flickering
    (.setProjectionMatrix batch (.combined camera))
    (.begin batch)
    (renderfn)
    (.end batch)))

(defn render-gui   [renderfn] (render-with   gui/unit-scale   gui/camera renderfn))
(defn render-world [renderfn] (render-with world/unit-scale world/camera renderfn))

(defn- default-components [{:keys [tile-size screens]}]
  [[:gdl.gdx]
   [:gdl.assets {:folder "resources/" ; TODO these are classpath settings ?
                 :sounds-folder "sounds/"
                 :sound-files-extensions #{"wav"}
                 :image-files-extensions #{"png" "bmp"}
                 :log-load-assets? false}]
   [:gdl.graphics.gui]
   [:gdl.graphics.world (or tile-size 1)]
   [:gdl.graphics.font]
   [:gdl.graphics.batch]
   [:gdl.graphics.shape-drawer]  ; after :gdl.graphics.batch
   [:gdl.ui]
   [:gdl.app screens]])

(defn- apply-ns-components
  "Given a map of components where keywords represent namespaces
  Dispatches on the namespace object via ns-find.

  Requires namespaces which could not be found with find-ns.

  assert's if a namespace can not be found even after require."
  [system components log?]
  (doseq [[k v] components
          :let [ns-sym (-> k name symbol)
                _ (when-not (find-ns ns-sym)
                    (require ns-sym))
                ns-obj (find-ns ns-sym)]]
    (assert ns-obj (str "Could not find-ns " ns-sym))
    (when log?
      (println (symbol system) ">" k))
    (system [ns-obj v])))

(defn- ->Game [{:keys [log-lc?  ns-components]
                :as config}]
  (let [components (concat (default-components config)
                           ns-components)
        _ (when log-lc?
            (clojure.pprint/pprint components))
        apply! #(apply-ns-components % components log-lc?)]
    (proxy [Game] []
      (create  [] (apply! #'lc/create))
      (dispose [] (apply! #'lc/dispose))
      (render []
        (ScreenUtils/clear color/black)
        (fix-viewport-update)
        ;(proxy-super render) ; fix for reflection warning (https://clojure.atlassian.net/browse/CLJ-1433)
        (proxy-call-with-super #(.render ^Game this) this "render"))
      (resize [w h]
        (on-resize w h)))))

(defn start [{:keys [window] :as config}]
  (lwjgl3/create-app (->Game config)
                     window))
