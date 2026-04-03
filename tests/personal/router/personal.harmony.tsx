import React from 'react';
import PersonalDeaultHarmony from '../pages/personalpage/index.native';

const PersonalRouters = ({ defaultRoute, ...personalProps }) => {
  // 个人中心不需要路由，减少嵌套层级
  return <PersonalDeaultHarmony {...personalProps} />;
};
export default PersonalRouters;
