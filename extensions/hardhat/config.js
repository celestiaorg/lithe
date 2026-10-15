export default async () => ({
  validateUserConfig: async (userConfig) => {
    const lithe = userConfig.lithe;
    if (lithe === undefined) return [];
    if (typeof lithe !== "object" || lithe === null) {
      return [{ path: ["lithe"], message: "Expected an object" }];
    }
    const errors = [];
    if (lithe.path !== undefined && typeof lithe.path !== "string") {
      errors.push({ path: ["lithe", "path"], message: "Expected a string" });
    }
    if (lithe.checkSpecs !== undefined && typeof lithe.checkSpecs !== "boolean") {
      errors.push({ path: ["lithe", "checkSpecs"], message: "Expected a boolean" });
    }
    return errors;
  },

  resolveUserConfig: async (userConfig, resolveConfigurationVariable, next) => {
    const resolved = await next(userConfig, resolveConfigurationVariable);
    return {
      ...resolved,
      lithe: {
        path: userConfig.lithe?.path ?? "lithe",
        checkSpecs: userConfig.lithe?.checkSpecs ?? false,
      },
    };
  },
});
