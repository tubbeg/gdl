(ns gdl.game
  (:require [gdl.lc :as lc]
            [gdl.gdx :as gdx]
            [gdl.graphics :as g]
            [gdl.graphics.color :as color]
            [gdl.graphics.gui :as gui]
            [gdl.graphics.world :as world]
            [gdl.backends.lwjgl3 :as lwjgl3])
  (:import com.badlogic.gdx.Game
           com.badlogic.gdx.utils.ScreenUtils))

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

(defn- default-components [{:keys [tile-size]}]
  [[:gdl.gdx] ; gdx globals link vars
   [:gdl.assets {:folder "resources/" ; TODO these are classpath settings ?
                 :sounds-folder "sounds/"
                 :sound-files-extensions #{"wav"}
                 :image-files-extensions #{"png" "bmp"}
                 :log-load-assets? false}]
   [:gdl.graphics.gui] ; gui viewport/camera
   [:gdl.graphics.world (or tile-size 1)] ; world viewport/camera
   [:gdl.graphics.font] ; default-font
   [:gdl.graphics.batch] ; sprite-batch
   [:gdl.graphics.shape-drawer]  ; after :gdl.graphics.batch
   [:gdl.ui] ; skin
   ])

(defn- apply-ns-components
  "Given a map of components where keywords represent namespaces
  Dispatches on the namespace object via ns-find.

  Requires namespaces which could not be found with find-ns.

  assert's if a namespace can not be found even after require."
  [system components log?]
  (doseq [[k v] components
          :let [ns-sym (-> k name symbol)
                _ (when-not (find-ns ns-sym) (require ns-sym))
                ns-obj (find-ns ns-sym)]]
    (assert ns-obj (str "Could not find-ns " ns-sym))
    (when log? (println (symbol system) ">" k))
    (system [ns-obj v])))

(defn- ->Game [{:keys [log-lc? ns-components] :as config}]
  (let [components (concat (default-components config)
                           ns-components
                           [[:gdl.app (:screens config)]]) ; app after other
        apply! #(apply-ns-components % components log-lc?)]
    (when log-lc? (clojure.pprint/pprint components))
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
