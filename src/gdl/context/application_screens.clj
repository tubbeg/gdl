(ns gdl.context.application-screens
  (:require [gdl.context :refer [current-screen]]
            [gdl.screen :as screen]))

(extend-type gdl.context.Context
  gdl.context/ApplicationScreens
  (current-screen [{:keys [context/current-screen] :as context}]
    (get context current-screen))

  (change-screen [context new-screen-key]
    (when-let [screen (current-screen context)]
      (screen/hide screen context))
    (let [screen (new-screen-key context)
          _ (assert screen (str "Cannot find screen with key: " new-screen-key))
          new-context (assoc context :context/current-screen new-screen-key)]
      (screen/show screen new-context)
      new-context)))
