export interface AnimationHeaderProps {
  /**
   * 单双wap样式
   */
  _styles     ;

  /**
   * mergeStyle
   */
  mergeStyle?     ;

  /**
   * 未登录文案
   */
  unLoginText?     ;

  /**
   * newMergeStyle
   */
  newMergeStyle     ;

  /**
   * 是否登录
   */
  isLogin         ;

  /**
   * 会员是否展示文案
   */
  showText         ;

  /**
   * vpro内容
   */
  item     ;

  /**
   * mergeStyle
   */
  showIcon         ;

  /**
   * 头像icon
   */
  avatarIcon              ;

  /**
   * 左边距
   */
  marginLeft        ;

  /**
   * 用户信息动画值
   */
  userInfoAnimatedValue     ;

  /**
   * 标题动画值
   */
  titleAnimatedValue     ;

  /**
   * 用户新点击事件
   */
  userInfoClick(actionName              )      ;

  /**
   * 判断用户是否能点击
   */
  canClick         ;

  /**
   * 默认头像
   */
  defaultAvatar?        ;

  /**
   * 单框架默认登录头像
   */
  loginDefaultAvatar?        ;

  /**
   * 单框架默认未登录头像
   */
  unLoginDefaultAvatar?        ;

  /**
   * 点击登录方法
   */
  goLogin     ;

  /**
   * 用户名
   */
  userName        ;

  /**
   * 用户等级
   */
  userLevel        ;

  /**
   * 是否是会员
   */
  isMember         ;

  /**
   * 会员头像
   */
  avaImg        ;

  /**
   * 是否pad横屏
   */
  isPadH?         ;
}
